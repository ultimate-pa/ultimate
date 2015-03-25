package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import java.util.Collection;
import java.util.ListIterator;
import java.util.NoSuchElementException;

/**
 * A list implemented with a doubly linked list. The elements are stored
 * (and iterated over) in the same order that they are inserted.
 * 
 * @author Daniel Tischner
 * <i>(original by Robert Sedgewick and Kevin Wayne)</i>
 *
 * @param <Item> Item the list should contain
 */
public class DoublyLinkedList<Item> implements Iterable<Item> {
	/**
	 * Number of elements on the list.
	 */
    private int size;
    /**
     * Sentinel before first item.
     */
    private Node pre;
    /**
     * Sentinel after last item.
     */
    private Node post;
    
    /**
     * Creates a new empty doubly linked list.
     */
    public DoublyLinkedList() {
        pre  = new Node();
        post = new Node();
        pre.next = post;
        post.prev = pre;
    }
    
    /**
     * Linked list node helper data type.
     * 
     * @author Daniel Tischner
     * <i>(original by Robert Sedgewick and Kevin Wayne)</i>
     *
     */
    private class Node {
    	/**
    	 * Item of the node.
    	 */
        private Item item;
        /**
         * Next node.
         */
        private Node next;
        /**
         * Previous node.
         */
        private Node prev;
    }
    
    /**
     * Returns if the list is empty or not.
     * @return if the list is empty or not
     */
    public boolean isEmpty() {
    	return size == 0;
    }
    /**
     * Returns the size of the list.
     * @return size of the list
     */
    public int size() {
    	return size;
    }
    /**
     * Adds the given item to the list.
     * @param item Item to add
     */
    public void add(Item item) {
        Node last = post.prev;
        Node x = new Node();
        x.item = item;
        x.next = post;
        x.prev = last;
        post.prev = x;
        last.next = x;
        size++;
    }
    /**
     * Gets the iterator of the list.
     */
    public ListIterator<Item> iterator() {
    	return new DoublyLinkedListIterator();
    }

    // assumes no calls to DoublyLinkedList.add() during iteration
    /**
     * Iterator of the list. Assumes no calls to
     * {@link DoublyLinkedList#add(Object)} during iteration.
     * 
     * @author Daniel Tischner
     * <i>(original by Robert Sedgewick and Kevin Wayne)</i>
     *
     */
    private class DoublyLinkedListIterator implements ListIterator<Item> {
    	/**
    	 * The node that is returned by {@link #next()}.
    	 */
        private Node current = pre.next;
        /**
         * The last node to be returned by {@link #previous()}
         * or {@link #next()}.
         */
        private Node lastAccessed = null;
        /**
         * Current index of the iterator.
         */
        private int index = 0;
        
        @Override
        public boolean hasNext() {
        	return index < size;
        }
        @Override
        public boolean hasPrevious() {
        	return index > 0;
        }
        @Override
        public int previousIndex() {
        	return index - 1;
        }
        @Override
        public int nextIndex() {
        	return index;
        }
        @Override
        public Item next() {
            if (!hasNext()) {
            	throw new NoSuchElementException();
            }
            lastAccessed = current;
            Item item = current.item;
            current = current.next; 
            index++;
            return item;
        }
        @Override
        public Item previous() {
            if (!hasPrevious()) {
            	throw new NoSuchElementException();
            }
            current = current.prev;
            index--;
            lastAccessed = current;
            return current.item;
        }

        @Override
        public void set(Item item) {
            if (lastAccessed == null) {
            	throw new IllegalStateException();
            }
            lastAccessed.item = item;
        }

        @Override
        public void remove() { 
            if (lastAccessed == null) {
            	throw new IllegalStateException();
            }
            Node x = lastAccessed.prev;
            Node y = lastAccessed.next;
            x.next = y;
            y.prev = x;
            size--;
            if (current == lastAccessed) {
            	current = y;
            } else {
            	index--;
            }
            lastAccessed = null;
        }

        @Override
        public void add(Item item) {
            Node x = current.prev;
            Node y = new Node();
            Node z = current;
            y.item = item;
            x.next = y;
            y.next = z;
            z.prev = y;
            y.prev = x;
            size++;
            index++;
            lastAccessed = null;
        }

    }
    
    @Override
    public String toString() {
        StringBuilder s = new StringBuilder();
        for (Item item : this) {
        	s.append(item + " ");
        }
        return s.toString();
    }
}

