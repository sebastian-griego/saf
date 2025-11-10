from harness.normalize import normalize_lean_prop
import re

# Test what happens to ≠
test_cases = [
    "a ≠ b",
    "a ≥ b", 
    "¬ ∃ (x : ℕ), P x",
]

print("Testing normalization:")
for test in test_cases:
    print(f"\nInput: {repr(test)}")
    s0 = normalize_lean_prop(test, use_s1=False)
    print(f"S0:    {repr(s0)}")
    s1 = normalize_lean_prop(test, use_s1=True)
    print(f"S1:    {repr(s1)}")
    
    # Check if ≠ is in the string
    if "≠" in test:
        print(f"  ≠ in S0 result: {'≠' in s0}")
        print(f"  ≠ in S1 result: {'≠' in s1}")

