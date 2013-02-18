package local.stalin.util;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.lang.ref.WeakReference;
import java.lang.ref.ReferenceQueue;
import java.util.*;

/**
 * A UnifyHash is a collection that helps to implement the fly-weight
 * design pattern.  It stores a set of weak references to objects,
 * which can be retrieved by a hash code.  
 *
 * If you use the fly-weight design pattern consequently, you do not
 * need to override equals or hash code at all, as two objects that
 * equal are always the same.  Unfortunately, while you are creating a
 * new object, you need to check, if the same object already existed
 * and therefore have a method to compare for equality and to
 * calculate a hash code for the hash table used in this class.
 * Therefore you have to call the put/remove/unify methods with
 * some hash code calculated from the internal data.  Also the
 * unify method is called with a comparator, that checks for
 * equality.
 *
 * The way to use this class is as follows. First follow the
 * fly-weight design pattern and make the class immutable.  Make the
 * constructor private so it can't be called from outside the class.
 * Instead add a static method &quot;<code>create</code>&quot; that
 * creates new instances, or reuses old ones that have the same data:
 *
 * <pre>
 *     private static UnifyHash<MyObject> unifyHash;
 *
 *      **
 *      * Create a new instance of MyObject with parameters
 *      * "a" and "child", or returns an already existing one.
 *     public static MyObject create(int a, MyObject child) {
 *        int hashcode = a*0x12345679 + child.hashCode();
 *
 *         * First iterate the object with the same hashcode and
 *         * check if the same object is already present.
 *        for (MyObject o : unifyHash.iterateHashCode(hashcode)) {
 *            if (o.a == a && o.child == child) {
 *                return o;
 *            }
 *        }
 *         * Object was not found, create a new one and put it into
 *         * the unify hash.
 *        MyObject o = new MyObject(a, child);
 *        unifyHash.put(hashcode, o);
 *        return o;
 *    }
 * </pre>
 */
public class UnifyHash<E> extends AbstractCollection<E> implements Serializable {
    /**
	 * 
	 */
	private static final long serialVersionUID = 1679059685462061236L;

	/** 
     * the default capacity
     */
    private static final int DEFAULT_CAPACITY = 11;

    /** the default load factor of a HashMap */
    private static final float DEFAULT_LOAD_FACTOR = 0.75F;

    private transient ReferenceQueue<E> queue = new ReferenceQueue<E>();

    static class Bucket<E> extends WeakReference<E>
    {
    	public Bucket(E o, ReferenceQueue<E> q) {
    	    super(o, q);
    	}

    	int hash;
    	Bucket<E> next;
    }

    private transient Bucket<E>[] buckets;
    transient int modCount = 0;
    int size = 0;
    int threshold;
    float loadFactor;

    /**
     * Creates a new unify hash.
     * @param initialCapacity The initial number of hash buckets
     * @param loadFactor The maximum average number of objects per
     * buckets.
     */
    @SuppressWarnings("unchecked")
    public UnifyHash(int initialCapacity, float loadFactor) {
    	this.loadFactor = loadFactor;
    	buckets = new Bucket[initialCapacity];
    	threshold = (int) (loadFactor * initialCapacity);
    }

    /**
     * Creates a new unify hash with default load factor.
     * @param initialCapacity The initial number of hash buckets
     */
    public UnifyHash(int initialCapacity) {
    	this(initialCapacity, DEFAULT_LOAD_FACTOR);
    }

    /**
     * Creates a new unify hash with default initial size and
     * load factor.
     */
    public UnifyHash() {
    	this(DEFAULT_CAPACITY, DEFAULT_LOAD_FACTOR);
    }

    /**
     * This method is called when the number of objects is bigger than
     * loadFactor*buckets.length.  It doubles the number of buckets
     * and reorganizes the objects into the hash buckets.
     */
    @SuppressWarnings("unchecked")
    private void grow() {
    	Bucket<E>[] oldBuckets = buckets;
    	int newCap = buckets.length * 2 + 1;
    	threshold = (int) (loadFactor * newCap);
    	buckets = new Bucket[newCap];
    	for (int i = 0; i < oldBuckets.length; i++) {
    	    Bucket<E> nextBucket;
    	    for (Bucket<E> b = oldBuckets[i]; b != null; b = nextBucket) {
        		if (i != Math.abs(b.hash % oldBuckets.length))
        		    throw new RuntimeException(""+i+", hash: "+b.hash+
        					       ", oldlength: "
        					       +oldBuckets.length);
        		int newSlot = Math.abs(b.hash % newCap);
        		nextBucket = b.next;
        		b.next = buckets[newSlot];
        		buckets[newSlot] = b;
    	    }
    	}
    }

    /**
     * Clean up the hash table, by removing all weak references to objects
     * that are no longer existing.  This methods is already called from the
     * other public methods, so there is no need to call it manually.
     */
    @SuppressWarnings("unchecked")
    public final void cleanUp() {
    	Bucket<E> died;
    	while ((died = (Bucket<E>) queue.poll()) != null) {
    	    int diedSlot = Math.abs(died.hash % buckets.length);
    	    if (buckets[diedSlot] == died)
        		buckets[diedSlot] = died.next;
    	    else {
        		Bucket<E> b = buckets[diedSlot];
        		while (b.next != died)
        		    b = b.next;
        		b.next = died.next;
    	    }
    	    size--;
    	}
    }

    /**
     * The number of objects that are stored in this collection.
     */
    public int size() {
    	return size;
    }

    /**
     * Gets an iterator of all objects in this collection.
     */
    public Iterator<E> iterator() {
    	cleanUp();

    	return new Iterator<E>() {
    	    private int bucket = 0;
    	    private int known = modCount;
    	    private Bucket<E> nextBucket;
    	    private E nextVal;

    	    {
        		internalNext();
    	    }

    	    private void internalNext() {
        		while (true) {
        		    while (nextBucket == null) {
            			if (bucket == buckets.length)
            			    return;
            			nextBucket = buckets[bucket++];
        		    }
        		    
        		    nextVal = nextBucket.get();
        		    if (nextVal != null)
        			return;

        		    nextBucket = nextBucket.next;
        		}
    	    }

    	    public boolean hasNext() {
        		return nextBucket != null;
    	    }

    	    public E next() {
        		if (known != modCount)
        		    throw new ConcurrentModificationException();
        		if (nextBucket == null)
        		    throw new NoSuchElementException();
        		E result = nextVal;
        		nextBucket = nextBucket.next;
        		internalNext();
        		return result;
    	    }

    	    public void remove() {
        		throw new UnsupportedOperationException();
    	    }
    	};
    }

    /**
     * Gets an iterator of all objects in this collection with the
     * given hash code.
     */
    public Iterable<E> iterateHashCode(final int hash) {
    	cleanUp();
    	return new Iterable<E>() {
    		public Iterator<E> iterator() {
    			return new Iterator<E>() {
    	    	    private int known = modCount;
    	    	    private boolean removeOk = false;
    	    	    private Bucket<E> removeBucket = null;
    	    	    private Bucket<E> prevBucket   = null;
    	    	    private Bucket<E> nextBucket =
    	    	    	buckets[Math.abs(hash % buckets.length)];
    	    	    private E nextVal;

    	    	    {
    	        		internalNext();
    	    	    }

    	    	    private void internalNext() {
    	        		while (nextBucket != null) {
    	        		    if (nextBucket.hash == hash) {
    	            			nextVal = nextBucket.get();
    	            			if (nextVal != null)
    	            			    return;
    	        		    }
    	        		    prevBucket = nextBucket;
    	        		    nextBucket = nextBucket.next;
    	        		}
    	    	    }

    	    	    public boolean hasNext() {
    	        		return nextBucket != null;
    	    	    }

    	    	    public E next() {
    	        		if (known != modCount)
    	        		    throw new ConcurrentModificationException();
    	        		if (nextBucket == null)
    	        		    throw new NoSuchElementException();
    	        		E result = nextVal;
    	        		removeBucket = prevBucket;
    	        		removeOk = true;
    	        		prevBucket = nextBucket;
    	        		nextBucket = nextBucket.next;
    	        		internalNext();
    	        		return result;
    	    	    }

    	    	    public void remove() {
    	        		if (known != modCount)
    	        		    throw new ConcurrentModificationException();
    	        		if (!removeOk)
    	        		    throw new IllegalStateException();
    	        		if (removeBucket == null)
    	        		    buckets[Math.abs(hash % buckets.length)]
    	                			= buckets[Math.abs(hash % buckets.length)].next;
    	           		else
    	        		    removeBucket.next = removeBucket.next.next;
    	        		known = ++modCount;
    	        		size--;
    	    	    }
    	    	};
    		}
    	};
    }

    /**
     * Adds a new object into this collection.  There should be 
     * no "equal" object already in this collection.
     * @param hash the hash code of the object  (this does not need
     * to be equal to object.hashCode().
     * @param o the object to add to this collection.
     */
    public void put(int hash, E o) {
    	if (size++ > threshold)
    	    grow();
    	modCount++;

    	int slot = Math.abs(hash % buckets.length);
    	Bucket<E> b = new Bucket<E>(o, queue);
    	b.hash = hash;
    	b.next = buckets[slot];
    	buckets[slot] = b;
    }

    /**
     * Remove the object o from the collection.
     */
    public boolean remove(int hash, E o) {
    	Iterator<E> i = iterateHashCode(hash).iterator();
    	while (i.hasNext()) {
    	    if (i.next() == o) {
        		i.remove();
        		return true;
    	    }
    	}
    	return false;
    }

    /**
     * Adds an object to this collection or returns a reference to
     * an existing object from the collection.  
     * It is often easier to not use this function and use something
     * similar to the example method in the class description.  This
     * way you do not need to create a Comparator class and create
     * unnecessary objects.
     * 
     * @param o the object to add to this collection.
     * @param hash the hash code of the object. This does not need
     * to be equal to object.hashCode(), but objects that compare equal
     * by comparator should have the same hash code.
     * @param comparator a comparator that determines if an object
     * in this hash is equal to the object o.
     * @return An object from the hash that equals o, or if no such
     * object exists adds o to the collection and returns o.
     */
    public E unify(E o, int hash, Comparator<E> comparator) {
    	cleanUp();
    	int slot = Math.abs(hash % buckets.length);
    	for (Bucket<E> b = buckets[slot]; b != null; b = b.next) {
    		if (b.hash == hash) {
    			E old = b.get();
    			if (old != null && comparator.compare(o, old) == 0)
    				return old;
    		}
    	}

    	put(hash, o);
    	return o;
    }
    private void writeObject(ObjectOutputStream oos) throws IOException {
    	oos.defaultWriteObject();
    	oos.writeInt(buckets.length);
    	for (Bucket<E> b : buckets) {
    		while (b != null) {
    			E elem = b.get();
    			if (elem != null) {
	    			oos.writeInt(b.hash);
	    			oos.writeObject(elem);
    			}
    			b = b.next;
    		}
    	}
    	// Finish with <0,Null>
    	oos.writeInt(0);
    	oos.writeObject(null);
    }
    @SuppressWarnings("unchecked")
	private void readObject(ObjectInputStream ois) 
    throws IOException, ClassNotFoundException {
    	queue = new ReferenceQueue<E>();
    	modCount = 0;
    	ois.defaultReadObject();
    	int bucketsize = ois.readInt();
    	buckets = (Bucket<E>[])new Bucket[bucketsize];
    	while (true) {
    		int hash = ois.readInt();
    		E obj = (E)ois.readObject();
    		if (obj == null)
    			break;
    		put(hash,obj);
    	}
    }
}
