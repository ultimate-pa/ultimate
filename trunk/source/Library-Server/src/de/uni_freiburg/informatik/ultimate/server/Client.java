package de.uni_freiburg.informatik.ultimate.server;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.Socket;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CompletionStage;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.interactive.IInteractive;
import de.uni_freiburg.informatik.ultimate.interactive.IInteractiveQueue;
import de.uni_freiburg.informatik.ultimate.interactive.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.interactive.ITypeRegistry;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage.Action;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage.Message;
import de.uni_freiburg.informatik.ultimate.interactive.exceptions.ClientException;
import de.uni_freiburg.informatik.ultimate.interactive.exceptions.ClientQuittedException;
import de.uni_freiburg.informatik.ultimate.interactive.exceptions.ClientSorryException;

/**
 * represents a Client or possibly Future-Client. (separate class?) a Client that should implement the Ultimate
 * Interactive protocol
 * 
 * @author Julian Jarecki
 *
 */
public abstract class Client<T> {

	protected final ILogger mLogger;

	protected final Socket mSocket;

	protected final MessageQueue<T> mQueue;

	protected CompletableFuture<Client<T>> mHelloFuture = new CompletableFuture<>();
	protected boolean mQuitting = false;
	protected CompletableFuture<Void> mQuitFuture = new CompletableFuture<>();
	protected int mCurrentRequestId = 0;

	private ITypeRegistry<T> mTypeRegistry;
	private HandlerRegistry<T> mHandlerRegistry;

	private CompletableFuture<Void> mInputFuture;
	private CompletableFuture<Void> mOutputFuture;
	private CompletableFuture<Void> mFinishedFuture;

	private boolean mIOExceptionOccurred = false;

	Client(Socket connectionSocket, ILogger logger, ITypeRegistry<T> typeRegistry, IWrappedMessage<T> helloMessage) {
		mLogger = logger;

		mTypeRegistry = typeRegistry;
		mQueue = new MessageQueue<T>(logger, this::construct);
		mQueue.put(helloMessage);
		mHandlerRegistry = new HandlerRegistry<>(mTypeRegistry);
		mSocket = connectionSocket;
	}

	public CompletionStage<Client<T>> hasSaidHello() {
		return mHelloFuture;
	}

	public Future<Void> waitForQuit() {
		return mQuitFuture;
	}

	public IInteractive<T> createInteractiveInterface(CompletableFuture<IInteractiveQueue<Object>> common) {
		return new ClientInteractiveInterface(common);
	}

	private void warnUnregistered(String typeName) {
		mLogger.warn(String.format("received message with data of unregistered type \"%s\"", typeName));
	}

	protected void handle(IWrappedMessage<T> msg) {
		// mLogger.debug("handleWrappged: " + wrapped.header.toString());
		final String queryId = msg.getUniqueQueryIdentifier();
		final String typeName = msg.getUniqueDataTypeIdentifier();
		final String qTypeName = msg.getUniqueQueryDataTypeIdentifier();
		ITypeHandler<T> typeHandler = null;
		T data = msg.get();
		final boolean noDataType = typeName.isEmpty() && data == null;
		final boolean dataTypeUnregistered;
		if (mTypeRegistry.registered(typeName)) {
			dataTypeUnregistered = false;
			typeHandler = mHandlerRegistry.get(typeName);
		} else {
			dataTypeUnregistered = !noDataType;
		}
		Message logmsg = msg.getMessage();
		logmsg.log(mLogger);

		Action action = msg.getAction();
		switch (action) {
		case LOGGING:
			// if (!typeName.isEmpty())
			// log(data.toString(), logmsg.level);
			break;
		case SORRY:
		case SEND:
			if (dataTypeUnregistered) {
				warnUnregistered(typeName);
				break;
			}

			if (!mQueue.complete(queryId, data, action == Action.SORRY ? new ClientSorryException(msg) : null)) {
				// handle the message regularly, if the queryId is not one we
				// are waiting for
				typeHandler.consume(data);
			}
			break;
		case REQUEST:
			if (queryId.isEmpty()) {
				mLogger.warn("ignoring request message that has no Query attached");
				break;
			}
			if (!mTypeRegistry.registered(qTypeName)) {
				warnUnregistered(qTypeName);
			}
			typeHandler = mHandlerRegistry.get(qTypeName);
			if (data == null) {
				mQueue.answer(msg, typeHandler.supply());
			} else if (dataTypeUnregistered) {
				warnUnregistered(typeName);
				break;
			} else {
				mQueue.answer(msg, typeHandler.supply(data));
			}
			break;
		case QUIT:
			mLogger.info("Client has sent quit message. Shutting down connection.");
			mQuitting = true;
			break;
		case HELLO:
			mLogger.info("callign complete on completablefuture for hello: " + mHelloFuture.toString());
			mHelloFuture.complete(this);
			break;
		default:
			mLogger.warn("Received Message with unknown Action: " + action);
			break;
		}
	};

	protected abstract IWrappedMessage<T> construct();

	public void closeConnection() {
		try {
			mSocket.close();
			mLogger.info("Connection closed.");
		} catch (IOException e) {
			mLogger.error("failed to shut down connection gracefully.", e);
			handleIoException(e);
		}
	}

	public void handleIoException(final IOException e) {
		mIOExceptionOccurred = true;
		mQuitFuture.completeExceptionally(e);
		mFinishedFuture.completeExceptionally(e);
		mHelloFuture.completeExceptionally(e);
		mQueue.completeAllFuturesExceptionally(e);
	}
	
	private Void forwardThrowable(final Throwable e) {
		mQuitFuture.completeExceptionally(e);
		mFinishedFuture.completeExceptionally(e);
		mHelloFuture.completeExceptionally(e);
		mQueue.completeAllFuturesExceptionally(e);
		return null;
	}

	public boolean hasIOExceptionOccurred() {
		return mIOExceptionOccurred;
	}

	public void startQueue(ExecutorService executor) throws IOException {
		InputStream input = mSocket.getInputStream();
		OutputStream output = mSocket.getOutputStream();

		mInputFuture = CompletableFuture.runAsync(() -> runOutput(output), executor);
		mOutputFuture = CompletableFuture.runAsync(() -> runInput(input, mTypeRegistry), executor);
		
		mInputFuture.exceptionally(this::forwardThrowable);
		mOutputFuture.exceptionally(this::forwardThrowable);

		mFinishedFuture = CompletableFuture.allOf(mInputFuture, mOutputFuture).thenRun(this::quit);
	}

	private void quit() {
		mQueue.completeAllFuturesExceptionally(new ClientQuittedException());

		closeConnection();
		if (mQuitting)
			mQuitFuture.complete(null);
	}

	public Future<?> finished() {
		if (mFinishedFuture == null) {
			throw new RuntimeException("Clients Streams have not started");
		}

		return mFinishedFuture;
	}

	private void runOutput(OutputStream output) {
		IWrappedMessage<T> msg;
		while (!mQuitting) {
			msg = mQueue.poll(5, TimeUnit.SECONDS);
			if (msg == null)
				continue;

			try {
				msg.writeTo(output);
			} catch (IOException e) {
				mLogger.error(e);
				handleIoException(e);
				break;
			}
		}
	}

	private void runInput(InputStream input, ITypeRegistry<T> typeRegistry) {
		IWrappedMessage<T> msg;
		while (!mQuitting) {
			try {
				msg = construct();
				if (msg == null) {
					mLogger.error("Queue created null message.");
					break;
				}
				msg.readFrom(input, typeRegistry);
				try {
					handle(msg);
				} catch (Exception e) {
					String emsg = String.format("failed to handle %s message (%s).", msg.getAction(),
							msg.getUniqueQueryDataTypeIdentifier());
					mLogger.error(emsg, e);
					continue;
				}
			} catch (IOException e) {
				mLogger.error("failed to read input", e);
				handleIoException(e);
				return;
			} catch (InterruptedException e) {
				mLogger.error("input thread interrupted.", e);
				continue;
			}
		}
	}

	public class ClientInteractiveInterface implements IInteractive<T> {
		private final CompletableFuture<IInteractiveQueue<Object>> mCommonInterface;

		public ClientInteractiveInterface(CompletableFuture<IInteractiveQueue<Object>> commonInterface) {
			mCommonInterface = commonInterface;
		}

		@Override
		public <T1 extends T> void register(Class<T1> type, Consumer<T1> consumer) {
			mHandlerRegistry.register(type, consumer);
		}

		@Override
		public <T1 extends T> void register(Class<T1> type, Supplier<T1> supplier) {
			mHandlerRegistry.register(type, supplier);
		}

		@Override
		public <D extends T, T1 extends T> void register(Class<T1> type, Class<D> dataType, Function<D, T1> supplier) {
			mHandlerRegistry.register(type, dataType, supplier);
		}

		@Override
		public void send(T data) {
			mQueue.send(data);
		}

		@Override
		public <T1 extends T> CompletableFuture<T1> request(Class<T1> type) {
			return mQueue.request(type);
		}

		@Override
		public <T1 extends T> CompletableFuture<T1> request(Class<T1> type, T data) {
			return mQueue.request(type, data);
		}

		@Override
		public IInteractiveQueue<Object> common() {
			return mCommonInterface.getNow(IInteractiveQueue.dummy());
		}

	}

}