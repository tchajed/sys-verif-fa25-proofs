package heap_test

import (
	"sys_verif_code/heap"
	"testing"
)

func TestFindMajority(t *testing.T) {
	tests := []struct {
		name     string
		input    []uint32
		expected uint32
	}{
		{
			name:     "simple majority",
			input:    []uint32{1, 1, 2, 1, 1},
			expected: 1,
		},
		{
			name:     "interspersed majority",
			input:    []uint32{1, 2, 1, 2, 1},
			expected: 1,
		},
		{
			name:     "majority at the end",
			input:    []uint32{2, 2, 1, 1, 1},
			expected: 1,
		},
		{
			name:     "single element",
			input:    []uint32{1},
			expected: 1,
		},
		{
			name:     "two elements majority",
			input:    []uint32{1, 1},
			expected: 1,
		},
		{
			name:     "three elements majority",
			input:    []uint32{1, 2, 1},
			expected: 1,
		},
		{
			name:     "five elements with 3 majority",
			input:    []uint32{1, 2, 3, 1, 1},
			expected: 1,
		},
		{
			name:     "even length with majority",
			input:    []uint32{1, 1, 1, 1, 2, 3},
			expected: 1,
		},
		{
			name:     "another majority test",
			input:    []uint32{3, 3, 4, 2, 4, 4, 2, 4, 4},
			expected: 4,
		},
	}

	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			got := heap.FindMajority(tt.input)
			if got != tt.expected {
				t.Errorf("FindMajority(%v) = %d, want %d (test %s)", tt.input, got, tt.expected, tt.name)
			}
		})
	}
}
