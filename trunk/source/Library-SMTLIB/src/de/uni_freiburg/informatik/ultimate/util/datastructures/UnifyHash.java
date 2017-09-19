/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.util.datastructures;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.lang.ref.ReferenceQueue;
import java.lang.ref.WeakReference;
import java.util.AbstractCollection;
import java.util.Comparator;
import java.util.ConcurrentModificationException;
import java.util.Iterator;
import java.util.NoSuchElementException;

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
public class UnifyHash<E> extends AbstractCollection<E> {
    /** 
     * the default capacity
     */
    private static final int DEFAULT_CAPACITY = 11;

    /** the default load factor of a HashMap */
    private static final float DEFAULT_LOAD_FACTOR = 0.75F;

    private transient ReferenceQueue<E> mQueue = new ReferenceQueue<E>();

    static class Bucket<E> extends WeakReference<E> {
    	public Bucket(E o, ReferenceQueue<E> q) {
    	    super(o, q);
    	}

    	int mHash;
    	Bucket<E> mNext;
    }

    private transient Bucket<E>[] mBuckets;
    transient int mModCount = 0;
    int mSize = 0;
    int mThreshold;
    float mLoadFactor;

    /**
     * Creates a new unify hash.
     * @param initialCapacity The initial number of hash buckets
     * @param loadFactor The maximum average number of objects per
     * buckets.
     */
    @SuppressWarnings("unchecked")
    public UnifyHash(int initialCapacity, float loadFactor) {
    	this.mLoadFactor = loadFactor;
    	mBuckets = new Bucket[initialCapacity];
    	mThreshold = (int) (loadFactor * initialCapacity);
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
    	final Bucket<E>[] oldBuckets = mBuckets;
    	final int newCap = mBuckets.length * 2 + 1;
    	mThreshold = (int) (mLoadFactor * newCap);
    	mBuckets = new Bucket[newCap];
    	for (int i = 0; i < oldBuckets.length; i++) {
    	    Bucket<E> nextBucket;
    	    for (Bucket<E> b = oldBuckets[i]; b != null; b = nextBucket) {
        		if (i != Math.abs(b.mHash % oldBuckets.length)) {
					throw new RuntimeException(i + ", hash: " + b.mHash
        					       + ", oldlength: "
        					       + oldBuckets.length);
				}
        		final int newSlot = Math.abs(b.mHash % newCap);
        		nextBucket = b.mNext;
        		b.mNext = mBuckets[newSlot];
        		mBuckets[newSlot] = b;
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
    	while ((died = (Bucket<E>) mQueue.poll()) != null) {
    	    final int diedSlot = Math.abs(died.mHash % mBuckets.length);
    	    if (mBuckets[diedSlot] == died) {
				mBuckets[diedSlot] = died.mNext;
			} else {
        		Bucket<E> b = mBuckets[diedSlot];
        		while (b.mNext != died) {
					b = b.mNext;
				}
        		b.mNext = died.mNext;
    	    }
    	    mSize--;
    	}
    }

    /**
     * The number of objects that are stored in this collection.
     */
    @Override
	public int size() {
    	return mSize;
    }

    /**
     * Gets an iterator of all objects in this collection.
     */
    @Override
	public Iterator<E> iterator() {
    	cleanUp();

    	return new Iterator<E>() {
    	    private int mBucket = 0;
    	    private final int mKnown = mModCount;
    	    private Bucket<E> mNextBucket;
    	    private E mNextVal;

    	    {
        		internalNext();
    	    }

    	    private void internalNext() {
        		while (true) {
        		    while (mNextBucket == null) {
            			if (mBucket == mBuckets.length) {
							return;
						}
            			mNextBucket = mBuckets[mBucket++];
        		    }
        		    
        		    mNextVal = mNextBucket.get();
        		    if (mNextVal != null) {
						return;
					}

        		    mNextBucket = mNextBucket.mNext;
        		}
    	    }

    	    @Override
			public boolean hasNext() {
        		return mNextBucket != null;
    	    }

    	    @Override
			public E next() {
        		if (mKnown != mModCount) {
					throw new ConcurrentModificationException();
				}
        		if (mNextBucket == null) {
					throw new NoSuchElementException();
				}
        		final E result = mNextVal;
        		mNextBucket = mNextBucket.mNext;
        		internalNext();
        		return result;
    	    }

    	    @Override
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
    		@Override
			public Iterator<E> iterator() {
    			return new Iterator<E>() {
    	    	    private int mKnown = mModCount;
    	    	    private boolean mRemoveOk = false;
    	    	    private Bucket<E> mRemoveBucket = null;
    	    	    private Bucket<E> mPrevBucket   = null;
    	    	    private Bucket<E> mNextBucket =
    	    	    	mBuckets[Math.abs(hash % mBuckets.length)];
    	    	    private E mNextVal;

    	    	    {
    	        		internalNext();
    	    	    }

    	    	    private void internalNext() {
    	        		while (mNextBucket != null) {
    	        		    if (mNextBucket.mHash == hash) {
    	            			mNextVal = mNextBucket.get();
    	            			if (mNextVal != null) {
									return;
								}
    	        		    }
    	        		    mPrevBucket = mNextBucket;
    	        		    mNextBucket = mNextBucket.mNext;
    	        		}
    	    	    }

    	    	    @Override
					public boolean hasNext() {
    	        		return mNextBucket != null;
    	    	    }

    	    	    @Override
					public E next() {
    	        		if (mKnown != mModCount) {
							throw new ConcurrentModificationException();
						}
    	        		if (mNextBucket == null) {
							throw new NoSuchElementException();
						}
    	        		final E result = mNextVal;
    	        		mRemoveBucket = mPrevBucket;
    	        		mRemoveOk = true;
    	        		mPrevBucket = mNextBucket;
    	        		mNextBucket = mNextBucket.mNext;
    	        		internalNext();
    	        		return result;
    	    	    }

    	    	    @Override
					public void remove() {
    	        		if (mKnown != mModCount) {
							throw new ConcurrentModificationException();
						}
    	        		if (!mRemoveOk) {
							throw new IllegalStateException();
						}
    	        		if (mRemoveBucket == null) {
							mBuckets[Math.abs(hash % mBuckets.length)]
    	                		= mBuckets[Math.abs(hash % mBuckets.length)]
    	                					.mNext;
						} else {
							mRemoveBucket.mNext = mRemoveBucket.mNext.mNext;
						}
    	        		mKnown = ++mModCount;
    	        		mSize--;
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
    	if (mSize++ > mThreshold) {
			grow();
		}
    	mModCount++;

    	final int slot = Math.abs(hash % mBuckets.length);
    	final Bucket<E> b = new Bucket<E>(o, mQueue);
    	b.mHash = hash;
    	b.mNext = mBuckets[slot];
    	mBuckets[slot] = b;
    }

    /**
     * Remove the object o from the collection.
     */
    public boolean remove(int hash, E o) {
    	final Iterator<E> i = iterateHashCode(hash).iterator();
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
    	final int slot = Math.abs(hash % mBuckets.length);
    	for (Bucket<E> b = mBuckets[slot]; b != null; b = b.mNext) {
    		if (b.mHash == hash) {
    			final E old = b.get();
    			if (old != null && comparator.compare(o, old) == 0) {
					return old;
				}
    		}
    	}

    	put(hash, o);
    	return o;
    }
    /**
     * Specialized form that takes the hash code from the object and compares
     * with {@link Object#equals(Object) equals}.
     * @param o Object to unify.
     * @return Unified object.
     */
    public E unify(E o) {
    	cleanUp();
    	final int hash = o.hashCode();
    	final int slot = Math.abs(hash % mBuckets.length);
    	for (Bucket<E> b = mBuckets[slot]; b != null; b = b.mNext) {
    		if (b.mHash == hash) {
    			final E old = b.get();
    			if (old != null && o.equals(old)) {
					return old;
				}
    		}
    	}

    	put(hash, o);
    	return o;
    }
    private void writeObject(ObjectOutputStream oos) throws IOException {
    	oos.defaultWriteObject();
    	oos.writeInt(mBuckets.length);
    	for (Bucket<E> b : mBuckets) {
    		while (b != null) {
    			final E elem = b.get();
    			if (elem != null) {
	    			oos.writeInt(b.mHash);
	    			oos.writeObject(elem);
    			}
    			b = b.mNext;
    		}
    	}
    	// Finish with <0,Null>
    	oos.writeInt(0);
    	oos.writeObject(null);
    }
    @SuppressWarnings("unchecked")
	private void readObject(ObjectInputStream ois) 
		throws IOException, ClassNotFoundException {
    	mQueue = new ReferenceQueue<E>();
    	mModCount = 0;
    	ois.defaultReadObject();
    	final int bucketsize = ois.readInt();
    	mBuckets = new Bucket[bucketsize];
    	while (true) {
    		final int hash = ois.readInt();
    		final E obj = (E)ois.readObject();
    		if (obj == null) {
				break;
			}
    		put(hash,obj);
    	}
    }
}
