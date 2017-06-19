package de.uni_freiburg.informatik.ultimate.server;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.TimeUnit;
import java.util.function.Consumer;
import java.util.function.Supplier;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.interactive.IInteractiveQueue;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage.Action;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage.Writer;

public class MessageQueue<T> implements IInteractiveQueue<T> {
	private static final int QUEUE_SIZE = 1000;

	protected final BlockingQueue<IWrappedMessage<T>> mOutputBuffer;
	protected final Map<String, CompletableFuture<? extends T>> mFutureMap;
	protected final List<CompletableFuture<?>> mRegisteredFutures;

	private final ILogger mLogger;

	private final Supplier<IWrappedMessage<T>> mFactory;

	public MessageQueue(final ILogger logger, final Supplier<IWrappedMessage<T>> factory) {
		mLogger = logger;
		mFactory = factory;

		mOutputBuffer = new ArrayBlockingQueue<>(QUEUE_SIZE);
		mRegisteredFutures = new ArrayList<>();
		mFutureMap = new HashMap<>();
	}

	public IWrappedMessage<T> poll(final long timeout, final TimeUnit unit) {
		try {
			return mOutputBuffer.poll(5, TimeUnit.SECONDS);
		} catch (final InterruptedException e) {
			mLogger.error("output thread interrupted.", e);
			return null;
		}
	}

	public void put(final IWrappedMessage<T> msg) {
		try {
			mOutputBuffer.put(msg);
		} catch (final InterruptedException e) {
			mLogger.error("could not send message " + msg.toString(), e);
		}
	}

	private IWrappedMessage<T> put(final Consumer<Writer<T>> useWriter) {
		final IWrappedMessage<T> msg = mFactory.get();

		final Writer<T> writer = msg.writer();

		useWriter.accept(writer);

		writer.write();

		put(msg);

		return msg;
	}

	public void answer(final IWrappedMessage<?> query, final T data) {
		put(w -> w.setAction(Action.SEND).answer(query).setData(data));
	}

	@Override
	public void send(final T data) {
		put(w -> w.setAction(Action.SEND).setData(data));
	}

	@Override
	public <T1 extends T> CompletableFuture<T1> request(final Class<T1> type) {
		final IWrappedMessage<T> msg = put(w -> w.setAction(Action.REQUEST).setQuery(type));
		final CompletableFuture<T1> future = new CompletableFuture<>();
		mFutureMap.put(msg.getUniqueQueryIdentifier(), future);
		return future;
	}

	@Override
	public <T1 extends T> CompletableFuture<T1> request(final Class<T1> type, final T data) {
		final IWrappedMessage<T> msg = put(w -> w.setAction(Action.REQUEST).setQuery(type).setData(data));
		final CompletableFuture<T1> future = new CompletableFuture<>();
		mFutureMap.put(msg.getUniqueQueryIdentifier(), future);
		return future;
	}

	public <T1 extends T> boolean complete(final String qid, final T1 data, final Throwable e) {
		if (!mFutureMap.containsKey(qid))
			return false;
		final CompletableFuture<? extends T> future = mFutureMap.remove(qid);
		@SuppressWarnings("unchecked")
		final CompletableFuture<T1> castedFuture = (CompletableFuture<T1>) future;
		final boolean result = e == null ? castedFuture.complete(data) : castedFuture.completeExceptionally(e);
		if (!result) {
			mLogger.error("failed to complete request future, as it was already completed, but still registered with "
					+ this);
		}
		return result;
	}

	public boolean completeAllFuturesExceptionally(final Throwable ex) {
		return Stream.concat(mFutureMap.values().stream(), mRegisteredFutures.stream()).reduce(false,
				(r, f) -> f.completeExceptionally(ex), Boolean::logicalOr);
	}

	@Override
	public <V> CompletableFuture<V> newFuture() {
		final CompletableFuture<V> result = new CompletableFuture<V>();
		mRegisteredFutures.add(result);
		return result;
	}
}
