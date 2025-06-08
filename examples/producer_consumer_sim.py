import threading
import queue
import time
import random
from collections import defaultdict

class ProducerConsumerSimulator:
    """AI-generated simulator from TLA+ spec"""
    
    def __init__(self, num_producers, num_consumers, queue_capacity, max_value):
        self.queue = queue.Queue(maxsize=queue_capacity)
        self.produced = defaultdict(list)
        self.consumed = defaultdict(list)
        self.next_value = 1
        self.max_value = max_value
        self.value_lock = threading.Lock()
        
    def produce(self, producer_id):
        while True:
            with self.value_lock:
                if self.next_value > self.max_value:
                    break
                value = self.next_value
                self.next_value += 1
            
            try:
                self.queue.put(value, timeout=1)
                self.produced[producer_id].append(value)
                print(f"Producer {producer_id} produced: {value}")
                time.sleep(random.uniform(0.1, 0.3))
            except queue.Full:
                # Backoff and retry
                time.sleep(0.1)
                
    def consume(self, consumer_id):
        while True:
            try:
                value = self.queue.get(timeout=2)
                self.consumed[consumer_id].append(value)
                print(f"Consumer {consumer_id} consumed: {value}")
                time.sleep(random.uniform(0.2, 0.4))
            except queue.Empty:
                # Check if we're done
                with self.value_lock:
                    if self.next_value > self.max_value and self.queue.empty():
                        break

# Run simulation
if __name__ == "__main__":
    sim = ProducerConsumerSimulator(
        num_producers=2,
        num_consumers=2, 
        queue_capacity=3,
        max_value=10
    )

    producers = []
    consumers = []

    for i in range(2):
        p = threading.Thread(target=sim.produce, args=(f"P{i+1}",))
        producers.append(p)
        p.start()

    for i in range(2):
        c = threading.Thread(target=sim.consume, args=(f"C{i+1}",))
        consumers.append(c)
        c.start()

    for p in producers:
        p.join()
    for c in consumers:
        c.join()

    print("\nVerifying properties:")
    all_produced = set()
    for values in sim.produced.values():
        all_produced.update(values)
        
    all_consumed = set()
    for values in sim.consumed.values():
        all_consumed.update(values)
        
    print(f"Values produced: {sorted(all_produced)}")
    print(f"Values consumed: {sorted(all_consumed)}")
    print(f"No value lost: {all_produced == all_consumed}")