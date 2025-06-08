"""
Example of how AI can help interpret TLA+ error traces
This simulates what Claude does when analyzing traces
"""

class TraceStep:
    def __init__(self, state_num, action, variables):
        self.state_num = state_num
        self.action = action
        self.variables = variables

def analyze_counter_trace():
    """
    Simulated error trace from Counter spec showing race condition
    """
    trace = [
        TraceStep(1, "Init", {
            "counter": 0,
            "pc": {"1": "Get", "2": "Get"},
            "local": {"1": 0, "2": 0}
        }),
        TraceStep(2, "Get(1)", {
            "counter": 0,
            "pc": {"1": "Inc", "2": "Get"},
            "local": {"1": 0, "2": 0}
        }),
        TraceStep(3, "Get(2)", {
            "counter": 0,
            "pc": {"1": "Inc", "2": "Inc"},
            "local": {"1": 0, "2": 0}
        }),
        TraceStep(4, "Inc(1)", {
            "counter": 1,
            "pc": {"1": "Done", "2": "Inc"},
            "local": {"1": 0, "2": 0}
        }),
        TraceStep(5, "Inc(2)", {
            "counter": 1,  # Should be 2!
            "pc": {"1": "Done", "2": "Done"},
            "local": {"1": 0, "2": 0}
        })
    ]
    
    print("=== AI-Style Error Trace Analysis ===\n")
    print("SUMMARY: Race condition detected in counter increment\n")
    print("EXPLANATION:")
    print("1. Both processes read counter value 0 (steps 2-3)")
    print("2. Process 1 increments: 0 + 1 = 1 (step 4)")
    print("3. Process 2 also increments from its stale local value: 0 + 1 = 1 (step 5)")
    print("4. Final counter is 1 instead of expected 2\n")
    print("ROOT CAUSE: Non-atomic read-modify-write operation allows interleaving\n")
    print("FIX: Add synchronization or use atomic operations")
    
    return trace

# Run the analysis
if __name__ == "__main__":
    analyze_counter_trace()