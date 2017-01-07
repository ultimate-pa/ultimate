package de.uni_freiburg.informatik.ultimate.graphvr.server;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.TimeUnit;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.graphvr.protobuf.Meta.Header;
import de.uni_freiburg.informatik.ultimate.graphvr.protobuf.Meta.Header.Action;
import de.uni_freiburg.informatik.ultimate.graphvr.protobuf.Meta.Message;
import de.uni_freiburg.informatik.ultimate.graphvr.protobuf.Meta.Message.Level;

public class TCPServer {

	final static int PORT = 6789;
	protected final ILogger mLogger;
	protected int mPort;
	protected boolean mRunning = false;
	protected boolean mSaidHello = false;
	protected ServerSocket mSocket;

	protected Socket mClient = null;
	protected Thread mThread;

	protected Map<String, GeneratedMessageV3> mRegisteredTypes = new HashMap<>();

	protected ConcurrentLinkedQueue<GeneratedMessageV3> mInputBuffer;
	protected ConcurrentLinkedQueue<GeneratedMessageV3> mOutputBuffer;

	public TCPServer(ILogger logger, int port) {
		mLogger = logger;
		mPort = port;

		mInputBuffer = new ConcurrentLinkedQueue<>();
		mOutputBuffer = new ConcurrentLinkedQueue<>();
	}

	public synchronized void start() {
		mThread = new Thread(this::run);
		mRunning = true;
		mLogger.info("starting Server.");
		mThread.start();
	}

	public synchronized void stop() {
		mLogger.info("stopping Server..");
		mRunning = false;
		try {
			mThread.join();
			mLogger.info("Server stopped.");
		} catch (InterruptedException e) {
			mLogger.error("Server Thread was interrupted.", e);
		}
	}

	private void run() {
		try {
			mSocket = new ServerSocket(mPort);
		} catch (IOException e1) {
			mLogger.error("Server could not be started.", e1);
		}
		mClient = null;
		while (mRunning) {
			try {
				mLogger.info("listening on port " + mPort);
				mClient = mSocket.accept();
				notifyAll();
			} catch (IOException e) {
				mLogger.error("Could not listen on port:" + mPort);
				return;
			}

			InputStream input;
			OutputStream output;

			try {
				input = mClient.getInputStream();
				output = mClient.getOutputStream();

				TimeUnit.SECONDS.sleep(1);
				mClient.close();

				// Thread thread = new Thread(new
				// ServerConnection(connectionSocket,
				// mLogger));
				// thread.start();

				send("Hello over there! :D");

				while (mRunning) {
					if (mClient.isClosed()) {
						mLogger.error("connection was unexpectedly closed");
						break;
					}

					GeneratedMessageV3 msg = mOutputBuffer.poll();
					if (msg != null) {
						msg.writeDelimitedTo(output);
					}
				}

			} catch (IOException e) {
				mLogger.error("connection problem", e);
				continue;
			} catch (InterruptedException e) {
				mLogger.error("interrupted", e);
			}

		}
	}

	private void checkInitialized() {
		if (!mSaidHello)
			throw new IllegalStateException("You forgot to say Hello to the Client.");
	}

	public void hello(GeneratedMessageV3... messages) {
		send(Action.HELLO, messages);
		// TODO: expect hello back here.
		mSaidHello = true;
	}

	public void send(GeneratedMessageV3... messages) {
		checkInitialized();
		send(Action.SEND, messages);
	}

	public void request(GeneratedMessageV3... messages) {
		checkInitialized();
		send(Action.REQUEST, messages);
	}

	private synchronized void send(Action action, GeneratedMessageV3... messages) {
		final Header.Builder header = Header.newBuilder().setAction(action);
		Arrays.stream(messages).map(m -> m.getClass().getName()).forEachOrdered(header::addTypes);

		mOutputBuffer.add(header.build());
		Arrays.stream(messages).forEachOrdered(mOutputBuffer::add);
	}

	public synchronized void send(String msg) {
		final Message message = Message.newBuilder().setLevel(Level.INFO).setText(msg).build();
		final Header header = Header.newBuilder().setAction(Action.LOGGING).setMessage(message).build();

		mOutputBuffer.add(header);
	}

	// <T extends GeneratedMessageV3> T
	private synchronized void readToBuffer(final InputStream input) throws IOException {
		Header header = Header.parseDelimitedFrom(input);

		print(header.getMessage());

		for (String typeName : header.getTypesList()) {
			if (mRegisteredTypes.containsKey(typeName)) {
				final GeneratedMessageV3 datamsg = mRegisteredTypes.get(typeName).getParserForType()
						.parseDelimitedFrom(input);
				mOutputBuffer.add(datamsg);
			} else {
				
			}
		}		

		//mOutputBuffer.add(header);
	}

	public <T extends GeneratedMessageV3> void register(Class<T> type) {
		try {
			final String typeName = type.getName();
			final Method getDefaultInstance = type.getMethod("getDefaultInstance");
			if (mRegisteredTypes.containsKey(typeName)) {
				mLogger.warn("already registered type %s - will be overwritten.");
			}
			final Object defaultInstance = getDefaultInstance.invoke(null);
			mRegisteredTypes.put(typeName, (T) defaultInstance);
			mLogger.debug("Registered Types: " + String.join(" ", mRegisteredTypes.keySet()));
		} catch (NoSuchMethodException | SecurityException | IllegalAccessException | IllegalArgumentException
				| InvocationTargetException | ClassCastException e) {
			mLogger.error(String.format("Could not Register Class %s with Server.", type), e);
		}
	}

	private void print(final Message msg) {
		final String text = msg.getText();
		switch (msg.getLevel()) {
		case DEBUG:
			mLogger.debug(text);
			break;
		case INFO:
			mLogger.info(text);
			break;
		case WARN:
			mLogger.warn(text);
			break;
		case ERROR:
			mLogger.error(text);
			break;
		default:
			break;
		}
	}

	public void waitForConnection() {
		while (mClient == null || mClient.isClosed()) {
			try {
				mLogger.info("Waiting for connection.");
				wait(30000);
			} catch (InterruptedException e) {
				mLogger.error(e);
				continue;
			}
		}
	}

}