from harness.normalize import normalize_lean_prop

# Test cases
test_cases = [
    ("a ≠ b", "¬ (a = b)"),
    ("a ≥ b", "b ≤ a"),
    ("¬ ∃ (x : ℕ), P x", "∀ (x : ℕ), ¬ P x"),
    ("∀ a b : ℕ, a ≠ b → ¬ (a = b)", "∀ (a b : ℕ), ¬ (a = b) → ¬ (a = b)"),
    ("∀ a b : ℕ, a ≥ b → ∃ k, b + k = a", "∀ (a b : ℕ), b ≤ a → ∃ k, b + k = a"),
]

print("Testing S1 normalization:")
for input_str, expected in test_cases:
    result = normalize_lean_prop(input_str, use_s1=True)
    print(f"Input:  {input_str}")
    print(f"Result: {result}")
    print(f"Expect: {expected}")
    print(f"Match:  {result == expected}")
    print()
