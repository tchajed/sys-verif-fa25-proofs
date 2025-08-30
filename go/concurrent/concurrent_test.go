package concurrent

import (
	"sync"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestAtomicInt_Get(t *testing.T) {
	assert := assert.New(t)

	// Create a new AtomicInt
	i := NewAtomicInt()

	// Set the initial value
	i.Inc(42)

	// Get the value and assert it is correct
	result := i.Get()
	assert.Equal(uint64(42), result, "Get")

	// Increment the value
	i.Inc(10)

	// Get the updated value and assert it is correct
	result = i.Get()
	assert.Equal(uint64(52), result, "Get")
}

func TestAtomicInt_concurrent(t *testing.T) {
	assert := assert.New(t)

	i := NewAtomicInt()

	// Set an initial value
	i.Inc(42)

	var wg sync.WaitGroup
	wg.Add(100)
	// Increment the value concurrently
	for range 100 {
		go func() {
			i.Inc(1)
			wg.Done()
		}()
	}
	wg.Wait()

	// Get the updated value and assert it is correct
	result := i.Get()
	assert.Equal(uint64(142), result, "Get")
}

func TestParallelAdd2(t *testing.T) {
	assert := assert.New(t)

	for range 10 {
		result := ParallelAdd2()
		assert.Equal(uint64(4), result, "ParallelAdd2")
	}
}
