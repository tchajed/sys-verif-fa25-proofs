package barrier_test

import (
	"fmt"
	"sync/atomic"
	"sys_verif_code/concurrent/barrier"
	"testing"

	"github.com/stretchr/testify/assert"
)

func TestBarrierN(t *testing.T) {
	numRun := atomic.Int64{}
	b := barrier.New()
	b.Add(1)
	b.Add(2)
	for range 3 {
		go func() {
			numRun.Add(1)
			b.Done()
		}()
	}
	b.Wait()
	assert.Equal(t, numRun.Load(), int64(3))
}

func TestBarrierNoAdd(t *testing.T) {
	b := barrier.New()
	b.Wait()
}

func UseBarrierPrint() {
	b := barrier.New()
	for i := range 3 {
		b.Add(1)
		go func() {
			fmt.Printf("hello %d\n", i)
			b.Done()
		}()
	}
	b.Wait()

}
