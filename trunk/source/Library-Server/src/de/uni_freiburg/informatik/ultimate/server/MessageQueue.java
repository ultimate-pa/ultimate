package de.uni_freiburg.informatik.ultimate.server;

import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage;

public class MessageQueue<T> {
	private static final int QUEUE_SIZE = 1000;

	protected BlockingQueue<IWrappedMessage<T>> mOutputBuffer;

	private ILogger mLogger;

	public MessageQueue(ILogger logger) {
		mLogger = logger;

		mOutputBuffer = new ArrayBlockingQueue<>(QUEUE_SIZE);
	}

	public IWrappedMessage<T> poll(long timeout, TimeUnit unit) {
		try {
			return mOutputBuffer.poll(5, TimeUnit.SECONDS);
		} catch (InterruptedException e) {
			mLogger.error("output thread interrupted.", e);
			return null;
		}
	}
}
