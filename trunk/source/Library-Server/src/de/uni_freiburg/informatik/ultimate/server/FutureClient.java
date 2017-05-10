package de.uni_freiburg.informatik.ultimate.server;

import java.io.IOException;
import java.net.Socket;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.function.Function;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.interactive.ITypeRegistry;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage.Action;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage.Message;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage.Message.Level;

/**
 * represents possible Future-Client. <br>
 * The Client is obtained, as soon as
 * <ol>
 * <li>a connection is established</li>
 * <li>all necessary variables are provided,</li>
 * <li>client and Server have exchanged a "hello" message</li>
 * </ol>
 * 
 * @author Julian Jarecki
 *
 */
public class FutureClient<T> implements Future<Client<T>> {

	protected final ILogger mLogger;

	private final CompletableFuture<Socket> mSocket = new CompletableFuture<>();
	private final CompletableFuture<Supplier<IWrappedMessage<T>>> mMessageFactory = new CompletableFuture<>();
	private final CompletableFuture<ITypeRegistry<T>> mTypeRegistry = new CompletableFuture<>();
	private final CompletableFuture<ExecutorService> mExecutor = new CompletableFuture<>();
	private final CompletableFuture<Message> mHelloMessage = new CompletableFuture<IWrappedMessage.Message>();

	private final CompletableFuture<Client<T>> mClientFuture;
	private final Future<Client<T>> mClientWithHelloFuture;

	public FutureClient(final ILogger logger) {
		mLogger = logger;
		mClientFuture = CompletableFuture.allOf(mSocket, mMessageFactory, mTypeRegistry, mHelloMessage).thenApply(n -> {
			final Supplier<IWrappedMessage<T>> factory = mMessageFactory.join();
			final IWrappedMessage<T> hello = factory.get();
			hello.writer().setAction(Action.HELLO).setMessage(mHelloMessage.join()).write();
			return new Client<T>(mSocket.join(), logger, mTypeRegistry.join(), hello) {
				@Override
				protected IWrappedMessage<T> construct() {
					return factory.get();
				}

			};
		}).thenCombine(mExecutor, (c, e) -> {
			try {
				c.startQueue(e);
			} catch (final IOException e1) {
				throw new RuntimeException(e1);
			}
			return c;
		});
		mClientWithHelloFuture = mClientFuture.thenCompose(Client::hasSaidHello);
	}

	public void setSocket(final Socket socket) {
		if (!mSocket.complete(socket))
			throw new IllegalStateException("Socket had already been set");
	}

	public void setFactory(final Supplier<IWrappedMessage<T>> factory) {
		if (!mMessageFactory.complete(factory))
			throw new IllegalStateException("Message factory had already been set");
	}

	public void setRegistry(final ITypeRegistry<T> registry) {
		if (!mTypeRegistry.complete(registry))
			throw new IllegalStateException("Type registry had already been set");
	}
	
	public void setHelloMessage(final String source, final String text, final Level level) {
		final Message message = new Message(source, text, level);
		if (!mHelloMessage.complete(message))
			throw new IllegalStateException("Hello Message had already been set");
	}

	public void setExecutor(final ExecutorService executor) {
		if (!mExecutor.complete(executor))
			throw new IllegalStateException("Executor had already been set");
	}

	private static <R, T> T getNowFromFuture(final CompletableFuture<R> future, final Function<R, T> f, final T valueIfAbsent) {
		if (!future.isDone() || future.isCancelled() || future.isCompletedExceptionally())
			return valueIfAbsent;
		final R result = future.getNow(null);
		// if (result == null)
		// return valueIfAbsent;
		return f.apply(result);
	}

	public boolean isConnected() {
		return getNowFromFuture(mSocket, s -> s.isConnected(), false);
	}

	public boolean isClientRunning() {
		return getNowFromFuture(mClientFuture, s -> true, false);
	}

	@Override
	public boolean cancel(final boolean mayInterruptIfRunning) {
		return mClientWithHelloFuture.cancel(mayInterruptIfRunning);
	}

	@Override
	public boolean isCancelled() {
		return mClientWithHelloFuture.isCancelled();
	}

	@Override
	public boolean isDone() {
		return mClientWithHelloFuture.isDone();
	}

	@Override
	public Client<T> get() throws InterruptedException, ExecutionException {
		return mClientWithHelloFuture.get();
	}

	@Override
	public Client<T> get(final long timeout, final TimeUnit unit)
			throws InterruptedException, ExecutionException, TimeoutException {
		return mClientWithHelloFuture.get(timeout, unit);
	}

}