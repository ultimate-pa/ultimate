package util;

import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;;

public class Event {
	private final Lock lock = new ReentrantLock();
	private final Condition cond = lock.newCondition();
	private boolean flag;

	public void doWait() throws InterruptedException {
		lock.lock();
		try {
			while (!flag) {
				cond.await();
			}
		} finally {
			lock.unlock();
		}
	}

	public void doWait(final float seconds) throws InterruptedException {
		lock.lock();
		try {
			while (!flag) {
				cond.await((int) (seconds * 1000), TimeUnit.MILLISECONDS);
			}
		} finally {
			lock.unlock();
		}
	}

	public boolean isSet() {
		lock.lock();
		try {
			return flag;
		} finally {
			lock.unlock();
		}
	}

	public void set() {
		lock.lock();
		try {
			flag = true;
			cond.signalAll();
		} finally {
			lock.unlock();
		}
	}

	public void clear() {
		lock.lock();
		try {
			flag = false;
			cond.signalAll();
		} finally {
			lock.unlock();
		}
	}
}