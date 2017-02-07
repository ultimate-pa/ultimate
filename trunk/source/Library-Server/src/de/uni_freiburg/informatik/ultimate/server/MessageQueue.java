package de.uni_freiburg.informatik.ultimate.server;

import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.TimeUnit;
import java.util.function.Consumer;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.interactive.IInteractiveQueue;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage.Action;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage.Writer;

public class MessageQueue<T> implements IInteractiveQueue<T> {
	private static final int QUEUE_SIZE = 1000;

	protected BlockingQueue<IWrappedMessage<T>> mOutputBuffer;
	protected Map<String, CompletableFuture<? extends T>> mFutureMap;

	private ILogger mLogger;

	private Supplier<IWrappedMessage<T>> mFactory;

	public MessageQueue(ILogger logger, Supplier<IWrappedMessage<T>> factory) {
		mLogger = logger;
		mFactory = factory;

		mOutputBuffer = new ArrayBlockingQueue<>(QUEUE_SIZE);
		mFutureMap = new HashMap<>();
	}

	public IWrappedMessage<T> poll(long timeout, TimeUnit unit) {
		try {
			return mOutputBuffer.poll(5, TimeUnit.SECONDS);
		} catch (InterruptedException e) {
			mLogger.error("output thread interrupted.", e);
			return null;
		}
	}

	public void put(IWrappedMessage<T> msg) {
		try {
			mOutputBuffer.put(msg);
		} catch (InterruptedException e) {
			mLogger.error("could not send message " + msg.toString(), e);
		}
	}

	private IWrappedMessage<T> put(Consumer<Writer<T>> useWriter) {
		final IWrappedMessage<T> msg = mFactory.get();

		final Writer<T> writer = msg.writer();

		useWriter.accept(writer);

		writer.write();

		put(msg);

		return msg;
	}

	public void answer(IWrappedMessage<?> query, T data) {
		put(w -> w.setAction(Action.SEND).answer(query).setData(data));
	}

	@Override
	public void send(T data) {
		put(w -> w.setAction(Action.SEND).setData(data));
	}

	@Override
	public <T1 extends T> CompletableFuture<T1> request(Class<T1> type) {
		final IWrappedMessage<T> msg = put(w -> w.setAction(Action.REQUEST).setQuery(type));
		CompletableFuture<T1> future = new CompletableFuture<>();
		mFutureMap.put(msg.getUniqueQueryIdentifier(), future);
		return future;
	}

	@Override
	public <T1 extends T> CompletableFuture<T1> request(Class<T1> type, T data) {
		final IWrappedMessage<T> msg = put(w -> w.setAction(Action.REQUEST).setQuery(type).setData(data));
		CompletableFuture<T1> future = new CompletableFuture<>();
		mFutureMap.put(msg.getUniqueQueryIdentifier(), future);
		return future;
	}

	public <T1 extends T> boolean complete(String qid, T1 data, Throwable e) {
		if (!mFutureMap.containsKey(qid))
			return false;
		CompletableFuture<? extends T> future = mFutureMap.remove(qid);
		@SuppressWarnings("unchecked")
		CompletableFuture<T1> castedFuture = (CompletableFuture<T1>) future;
		final boolean result = e == null ? castedFuture.complete(data) : castedFuture.completeExceptionally(e);
		if (!result) {
			mLogger.error("failed to complete request future, as it was already completed, but still registered with "
					+ this);
		}
		return result;
	}
}
