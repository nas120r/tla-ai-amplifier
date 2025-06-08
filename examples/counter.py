import threading
import time
import random

class Counter:
    def __init__(self):
        self.value = 0
        self.lock = threading.Lock()
    
    def increment_unsafe(self):
        """Non-atomic increment (subject to race conditions)"""
        temp = self.value  # Get
        time.sleep(random.uniform(0.001, 0.01))  # Simulate processing
        self.value = temp + 1  # Inc
        
    def increment_safe(self):
        """Thread-safe increment"""
        with self.lock:
            temp = self.value
            self.value = temp + 1

# Example of race condition
counter = Counter()
threads = []

print("Testing unsafe increment (race condition possible):")
for i in range(5):
    t = threading.Thread(target=counter.increment_unsafe)
    threads.append(t)
    t.start()

for t in threads:
    t.join()

print(f"Final counter value: {counter.value} (expected: 5)")

# Example of safe implementation
counter = Counter()
threads = []

print("\nTesting safe increment (with lock):")
for i in range(5):
    t = threading.Thread(target=counter.increment_safe)
    threads.append(t)
    t.start()

for t in threads:
    t.join()

print(f"Final counter value: {counter.value} (expected: 5)")