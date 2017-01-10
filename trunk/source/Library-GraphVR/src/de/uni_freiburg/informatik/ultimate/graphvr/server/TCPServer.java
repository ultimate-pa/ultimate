package de.uni_freiburg.informatik.ultimate.graphvr.server;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.lang.reflect.InvocationTargetException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.function.Consumer;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.graphvr.protobuf.Meta.Header;
import de.uni_freiburg.informatik.ultimate.graphvr.protobuf.Meta.Header.Action;
import de.uni_freiburg.informatik.ultimate.graphvr.protobuf.Meta.Message;
import de.uni_freiburg.informatik.ultimate.graphvr.protobuf.Meta.Message.Level;

public class TCPServer implements IProtoServer {

	private static final String REQUEST_ID_PATTERN = "Request%s";
	protected final ILogger mLogger;
	protected int mPort;
	protected boolean mRunning = false;
	protected boolean mSaidHello = false;
	protected ServerSocket mSocket;

	protected Socket mClient = null;
	protected ExecutorService mExecutor;
	protected Future<?> mServerFuture;
	protected int mCurrentRequestId = 0;

	protected TypeRegistry mTypeRegistry = new TypeRegistry();
	protected Map<String, WrappedFuture<? extends GeneratedMessageV3>> mExpectedData = new HashMap<>();

	protected ConcurrentLinkedQueue<WrappedProtoMessage> mInputBuffer;
	protected ConcurrentLinkedQueue<GeneratedMessageV3> mOutputBuffer;

	public TCPServer(ILogger logger, int port) {
		mLogger = logger;
		mPort = port;

		mInputBuffer = new ConcurrentLinkedQueue<>();
		mOutputBuffer = new ConcurrentLinkedQueue<>();
		mExecutor = Executors.newWorkStealingPool();
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
			mServerFuture.get(20, TimeUnit.SECONDS);
			mLogger.info("Server stopped.");
		} catch (InterruptedException | ExecutionException e) {
			mLogger.error("Server Thread was interrupted.", e);
		} catch (TimeoutException e) {
			final boolean canceled = mServerFuture.cancel(true);
			mLogger.error(String.format("Server Thread Timed out. Canceled execution: %s", canceled), e);
			close();
		}
	}

	private void sendOutput() {
		OutputStream output;
		try {
			output = mClient.getOutputStream();
		} catch (IOException e) {
			mLogger.error("could not get Output stream", e);
			close();
			return;
		}
		while (mRunning) {
			if (mClient.isClosed()) {
				mLogger.error("connection was unexpectedly closed");
				break;
			}

			GeneratedMessageV3 msg = mOutputBuffer.poll();
			if (msg != null) {
				try {
					msg.writeDelimitedTo(output);
				} catch (IOException e) {

				}
			}
		}
	}

	private void handleInput() {
		InputStream input;
		try {
			input = mClient.getInputStream();
		} catch (IOException e) {
			mLogger.error("could not get Input stream", e);
			close();
			return;
		}
		while (mRunning) {
			if (mClient.isClosed()) {
				mLogger.error("connection was unexpectedly closed");
				break;
			}

			try {
				final WrappedProtoMessage wrapped = read(input);
				handleWrapped(wrapped);
			} catch (IOException e) {
				mLogger.error("failed to read input", e);
				close();
				return;
			}
		}
	}

	private void handleWrapped(final WrappedProtoMessage wrapped) {
		final String queryId = wrapped.header.getQueryId();
		final String typeName = wrapped.header.getDataType();
		switch (wrapped.header.getAction()) {
		case LOGGING:
			log(wrapped.data.toString(), wrapped.header.getMessage().getLevel());
			break;
		case SORRY:
			mLogger.info("Client says sorry.");
		case SEND:
			if (!mTypeRegistry.registered(typeName)) {
				mLogger.warn(String.format("received message with data of unregistered type %s", typeName));
				break;
			}
			final RegisteredType<?> wt = mTypeRegistry.get(typeName);
			if (mExpectedData.containsKey(queryId)) {
				final String wTypeName = wrapped.get().getDescriptorForType().getFullName();
				WrappedFuture<? extends GeneratedMessageV3> wf = mExpectedData.get(queryId);
				if (typeName != wTypeName) {
					mLogger.error(
							String.format("Expected %s, but client responded with type %s.", wTypeName, typeName));
				} else {
					wf.future.complete(wrapped.get());
				}
			} else {
				wt.consumer.accept(wrapped.get());
			}
			break;
		case REQUEST:
			if (queryId != null) {
				mLogger.error("handling client queries is not implemented yet.");
			} else {
				mLogger.warn("ignoring request message that has no Query attached");
				mLogger.warn(wrapped.header.toString());
			}
			break;
		case QUIT:
			break;
		case HELLO:
			break;
		default:
			break;
		}
	}

	private void close() {
		try {
			mClient.close();
			mSocket.close();
			mClient = null;
		} catch (IOException e) {
			mLogger.error("failed to shut down connection gracefully.", e);
			mClient = null;
			mSocket = null;
		}
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
			try {
				mLogger.info("listening on port " + mPort);
				mClient = mSocket.accept();
				synchronized (this) {
					notifyAll();
				}
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
			}

		}
	}

	private void checkInitialized() {
		if (!mSaidHello)
			throw new IllegalStateException("You forgot to say Hello to the Client. How unpolite of you.");
	}

	@Override
	public void hello(final GeneratedMessageV3 data) {
		send(Action.HELLO, data);
		// TODO: expect hello back here.
		mSaidHello = true;
	}

	@Override
	public void send(final GeneratedMessageV3 data) {
		checkInitialized();
		send(Action.SEND, data);
	}

	private String makeRequestId() {
		return String.format(REQUEST_ID_PATTERN, mCurrentRequestId++);
	}

	@Override
	public <T extends GeneratedMessageV3> CompletableFuture<T> request(final Class<T> type,
			final GeneratedMessageV3 data) {
		checkInitialized();
		if (!mTypeRegistry.registered(type))
			throw new IllegalArgumentException(String.format("Unregistered type: %s", type.getSimpleName()));

		final String requestId = makeRequestId();

		final Header header = getHeaderFor(data).setAction(Action.REQUEST).setQueryId(requestId)
				.setQueryType(type.getName()).build();
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

	private synchronized void send(Header header, GeneratedMessageV3 data) {
		mOutputBuffer.add(header);
		if (data != null)
			mOutputBuffer.add(data);
	}

	@Override
	public synchronized void send(String msg) {
		final Message message = Message.newBuilder().setLevel(Level.INFO).setText(msg).build();
		final Header header = Header.newBuilder().setAction(Action.LOGGING).setMessage(message).build();

		mOutputBuffer.add(header);
	}

	private WrappedProtoMessage read(final InputStream input) throws IOException {
		Header header = Header.parseDelimitedFrom(input);

		final String type = header.getDataType();

		print(header.getMessage());

		if (type == null) {
			return new WrappedProtoMessage(header, null);
		}
		if (mTypeRegistry.registered(type)) {
			final GeneratedMessageV3 datamsg = mTypeRegistry.get(type).defaultMsg.getParserForType()
					.parseDelimitedFrom(input);
			return new WrappedProtoMessage(header, datamsg);
		} else {
			throw new IllegalAccessError(String.format("received unregistered message type: %s", type));
		}
	}

	@Override
	public <T extends GeneratedMessageV3> void register(Class<T> type) {
		register(type, m -> {
		});
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

	private void print(final Message msg) {
		log(msg.getText(), msg.getLevel());
	}

	private void log(final String msg, Level level) {
		switch (level) {
		case DEBUG:
			mLogger.debug(msg);
			break;
		case INFO:
			mLogger.info(msg);
			break;
		case WARN:
			mLogger.warn(msg);
			break;
		case ERROR:
			mLogger.error(msg);
			break;
		default:
			break;
		}
	}

	@Override
	public void waitForConnection() {
		while (mClient == null || mClient.isClosed()) {
			try {
				mLogger.info("Waiting for connection.");
				synchronized (this) {
					wait(30000);
				}
			} catch (InterruptedException e) {
				mLogger.error(e);
				continue;
			}
		}
	}

}