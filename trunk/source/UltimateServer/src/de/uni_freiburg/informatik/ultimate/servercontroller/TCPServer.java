package de.uni_freiburg.informatik.ultimate.servercontroller;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.lang.reflect.InvocationTargetException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.ArrayBlockingQueue;
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.function.Consumer;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.server.FutureClient;
import de.uni_freiburg.informatik.ultimate.server.IServer;
import de.uni_freiburg.informatik.ultimate.server.ITypeRegistry;
import de.uni_freiburg.informatik.ultimate.server.exceptions.ClientSorryException;
import de.uni_freiburg.informatik.ultimate.server.exceptions.ConnectionInterruptedException;
import de.uni_freiburg.informatik.ultimate.server.protobuf.WrappedProtoMessage;
import de.uni_freiburg.informatik.ultimate.server.protobuf.Meta.Header;
import de.uni_freiburg.informatik.ultimate.server.protobuf.Meta.Header.Action;
import de.uni_freiburg.informatik.ultimate.server.protobuf.Meta.Message;
import de.uni_freiburg.informatik.ultimate.server.protobuf.Meta.Message.Level;

public abstract class TCPServer<T> implements IServer {

	private static final String REQUEST_ID_PATTERN = "Request%s";
	private static final String CLIENT_MESSAGE_PREFIX = "[Client] ";
	private static final int QUEUE_SIZE = 1000;

	protected final ILogger mLogger;
	protected int mPort;
	protected boolean mRunning = false;
	protected ServerSocket mSocket;

	protected FutureClient<T> mClient = null;
	protected ExecutorService mExecutor;
	protected Future<?> mServerFuture;

	protected final ITypeRegistry<T> mTypeRegistry;
	protected Map<String, WrappedFuture<? extends GeneratedMessageV3>> mExpectedData = new HashMap<>();

	protected BlockingQueue<GeneratedMessageV3> mOutputBuffer;

	public TCPServer(ILogger logger, int port) {
		mLogger = logger;
		mPort = port;

		mOutputBuffer = new ArrayBlockingQueue<>(QUEUE_SIZE);
		mExecutor = Executors.newWorkStealingPool();
		mClient = new Client(logger, mTypeRegistry);
	}

	@Override
	public synchronized void start() {
		mLogger.info("starting Server.");
		if (mExecutor.isTerminated()) {
			mExecutor = Executors.newWorkStealingPool();
		}
		mServerFuture = mExecutor.submit(this::run);
		mRunning = true;
	}

	@Override
	public synchronized void stop() {
		mLogger.info("stopping Server..");
		mRunning = false;
		try {
			mClient.closeConnection();
			mServerFuture.get(10, TimeUnit.SECONDS);
			mLogger.info("Server stopped.");
		} catch (InterruptedException | ExecutionException e) {
			mLogger.error("Server Thread was interrupted.", e);
		} catch (TimeoutException e) {
			final boolean canceled = mServerFuture.cancel(true);
			mLogger.error(String.format("Server Thread Timed out. Canceled execution: %s", canceled), e);
		}
	}

	private void sendOutput() {
		OutputStream output;
		try {
			output = mClient.getOutputStream();
		} catch (IOException e) {
			mLogger.error("could not get Output stream", e);
			closeClientConnection();
			return;
		}
		while (mRunning) {
			if (mClient.isClosed()) {
				mLogger.error("connection was unexpectedly closed");
				break;
			}

			GeneratedMessageV3 msg;
			try {
				// mLogger.info("trying to pull ... ");
				msg = mOutputBuffer.poll(5, TimeUnit.SECONDS);
				if (msg == null)
					continue;

				try {
					msg.writeDelimitedTo(output);
				} catch (IOException e) {
					mLogger.error(e);
					continue;
				}
			} catch (InterruptedException e) {
				mLogger.error("output thread interrupted.", e);
				continue;
			}
		}
	}

	private void handleInput() {
		InputStream input;
		try {
			input = mClient.getInputStream();
		} catch (IOException e) {
			mLogger.error("could not get Input stream", e);
			closeClientConnection();
			return;
		}
		while (mRunning) {
			if (mClient.isClosed()) {
				mLogger.error("connection was unexpectedly closed");
				break;
			}

			try {
				final WrappedProtoMessage wrapped = read(input);
				if (wrapped == null)
					break;
				handleWrapped(wrapped);
			} catch (IOException e) {
				mLogger.error("failed to read input", e);
				return;
			}
		}
	}

	private boolean failedAnyFuture(Throwable e) {
		return mExpectedData.values().stream().anyMatch(f -> f.future.completeExceptionally(e))
				|| (mHelloFuture != null && mHelloFuture.completeExceptionally(e));
	}

	private void run() {
		try {
			mSocket = new ServerSocket(mPort);
		} catch (IOException e1) {
			mLogger.error("Server could not be started.", e1);
			return;
		}
		mClient = null;
		while (mRunning) {
			mClientFuture = new CompletableFuture<Socket>();
			mHelloFuture = new CompletableFuture<Void>();
			try {
				mLogger.info("listening on port " + mPort);
				mClient = mSocket.accept();
				synchronized (this) {
					notifyAll();
				}
				mClientFuture.complete(mClient);
				send(Action.HELLO, null);
			} catch (IOException e) {
				mLogger.error("Could not listen on port:" + mPort);
				return;
			}

			// final List<Callable<Object>> runnables =
			// Arrays.asList(this::handleInput, this::sendOutput);
			// mExecutor.invokeAny(runnables);
			Future<?> InputMonitor = mExecutor.submit(this::handleInput);
			Future<?> OutputMonitor = mExecutor.submit(this::sendOutput);
			try {
				InputMonitor.get();
				OutputMonitor.get();
			} catch (InterruptedException | ExecutionException e) {
				mLogger.error("Input or outputstream halted.", e);
				failedAnyFuture(new ConnectionInterruptedException(e));
				closeClientConnection();
			}

		}
	}

	@Override
	public void send(final GeneratedMessageV3 data) {
		send(Action.SEND, data);
	}

	private String makeRequestId() {
		return String.format(REQUEST_ID_PATTERN, mCurrentRequestId++);
	}

	@Override
	public <T extends GeneratedMessageV3> CompletableFuture<T> request(final Class<T> type,
			final GeneratedMessageV3 data) {
		if (!isConnected())
			throw new IllegalArgumentException("No Client connected.");
		if (!mTypeRegistry.registered(type))
			throw new IllegalArgumentException(String.format("Unregistered type: %s", type.getSimpleName()));

		final String requestId = makeRequestId();

		final Header header = getHeaderFor(data).setAction(Action.REQUEST).setQueryId(requestId)
				.setQueryType(mTypeRegistry.get(type).registeredName()).build();

		mLogger.info(String.format("requested message of type %s from client", header.getQueryType()));

		send(header, data);

		final WrappedFuture<T> result = new WrappedFuture<>(type);
		mExpectedData.put(requestId, result);
		return result.future;
	}

	private Header.Builder getHeaderFor(GeneratedMessageV3 data) {
		final Header.Builder builder = Header.newBuilder();
		if (data != null) {
			builder.setDataType(RegisteredType.registeredName(data));
		}
		return builder;
	}

	private void send(Action action, GeneratedMessageV3 data) {
		final Header header = getHeaderFor(data).setAction(action).build();
		send(header, data);
	}

	private void send(Header header, GeneratedMessageV3 data) {
		sendWrapped(header);
		if (data != null)
			sendWrapped(data);
	}

	private void sendWrapped(GeneratedMessageV3 msg) {
		try {
			mOutputBuffer.put(msg);
		} catch (InterruptedException e) {
			mLogger.error("could not send message " + msg.toString(), e);
		}
	}

	@Override
	public synchronized void send(String msg) {
		final Message message = Message.newBuilder().setLevel(Level.INFO).setText(msg).build();
		final Header header = Header.newBuilder().setAction(Action.LOGGING).setMessage(message).build();

		sendWrapped(header);
	}

	private WrappedProtoMessage read(final InputStream input) throws IOException {
		Header header = Header.parseDelimitedFrom(input);

		if (header == null)
			return null;

		final String type = header.getDataType();

		print(header.getMessage());

		if (type.isEmpty()) {
			return new WrappedProtoMessage(header, null);
		}
		if (mTypeRegistry.registered(type)) {
			final GeneratedMessageV3 datamsg = mTypeRegistry.get(type).getDefaultInstance().getParserForType()
					.parseDelimitedFrom(input);
			return new WrappedProtoMessage(header, datamsg);
		} else {
			throw new IllegalAccessError(String.format("received unregistered message type: %s", type));
		}
	}

	@Override
	public <T extends GeneratedMessageV3> void register(Class<T> type, Consumer<T> consumer) {
		try {
			final String typeName = type.getName();
			if (mTypeRegistry.registered(type)) {
				mLogger.warn(String.format("already registered type %s - will be overwritten.", typeName));
			}
			mTypeRegistry.register(RegisteredType.newInstance(type, consumer));
			mLogger.info(mTypeRegistry);
		} catch (NoSuchMethodException | SecurityException | IllegalAccessException | IllegalArgumentException
				| InvocationTargetException | ClassCastException e) {
			mLogger.error(String.format("Could not Register Class %s with Server.", type), e);
		}
	}

	public void print(final Message msg) {
		log(msg.getText(), msg.getLevel());
	}

	public void log(final Message message) {
		log(message.getText(), message.getLevel());
	}

	public void log(final String msg, final Level level) {
		final Consumer<String> logmethod;
		switch (level) {
		case DEBUG:
			logmethod = mLogger::debug;
			break;
		case INFO:
			logmethod = mLogger::info;
			break;
		case WARN:
			logmethod = mLogger::warn;
			break;
		case ERROR:
			logmethod = mLogger::error;
			break;
		default:
			logmethod = mLogger::debug;
			break;
		}
		logmethod.accept(CLIENT_MESSAGE_PREFIX + msg);
	}

	@Override
	public void waitForConnection() throws InterruptedException {
		if (!mRunning || mServerFuture.isDone()) {
			throw new IllegalStateException("Server not running.");
		}
		if (mHelloFuture == null) {
			synchronized (this) {
				mLogger.info("waiting for connection ...");
				wait();
			}
		}
		mLogger.info("completablefuture for hello: " + mHelloFuture.toString());
		try {
			mHelloFuture.get(10, TimeUnit.SECONDS);
		} catch (ExecutionException e) {
			mLogger.error(e);
		} catch (TimeoutException e) {
			mLogger.info("completablefuture for hello timed out: " + mHelloFuture.toString());
			mLogger.error("timed out waiting for HELLO message from client.");
		}
	}

}