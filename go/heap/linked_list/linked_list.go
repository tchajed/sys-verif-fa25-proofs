package linked_list

type Node struct {
	elem uint64
	next *Node
}

func New() *Node {
	return nil
}

func (l *Node) Insert(elem uint64) *Node {
	return &Node{elem: elem, next: l}
}

func (l *Node) Pop() (uint64, *Node, bool) {
	if l == nil {
		return 0, l, false
	}
	return l.elem, l.next, true
}

func (l *Node) Contains(elem uint64) bool {
	var n = l
	for n != nil {
		if n.elem == elem {
			return true
		}
		n = n.next
	}
	return false
}

func (l *Node) Delete(elem uint64) *Node {
	if l == nil {
		return l
	}
	if l.elem == elem {
		// recurse to delete any copies
		return l.next.Delete(elem)
	}
	l.next = l.next.Delete(elem)
	return l
}

func (l *Node) Append(other *Node) *Node {
	if l == nil {
		return other
	}
	return &Node{elem: l.elem, next: l.next.Append(other)}
}
