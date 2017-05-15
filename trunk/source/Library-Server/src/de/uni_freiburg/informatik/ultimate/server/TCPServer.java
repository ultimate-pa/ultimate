package de.uni_freiburg.informatik.ultimate.server;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;
import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.interactive.ITypeRegistry;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage.Message.Level;
import util.Event;

public abstract class TCPServer<T> implements IInteractiveServer<T> {

	// private static final String CLIENT_MESSAGE_PREFIX = "[Client] ";

	protected final ILogger mLogger;
	protected int mPort;
	protected boolean mRunning = false;
	protected ServerSocket mSocket;

	// multiple Clients?
	protected FutureClient<T> mClient;
	protected ExecutorService mExecutor;
	protected Future<?> mServerFuture;
	protected Supplier<ExecutorService> mGetExecutorService;

	protected String mHelloMessage;

	protected boolean mCancelled;
	protected final Event mConnectionEvent;
	protected ITypeRegistry<T> mTypeRegistry;

	public TCPServer(final ILogger logger, final int port) {
		mLogger = logger;
		mPort = port;
		mGetExecutorService = Executors::newWorkStealingPool;
		mCancelled = false;
		mClient = new FutureClient<>(mLogger);
		mConnectionEvent = new Event();
		mConnectionEvent.set();
	}

	public abstract IWrappedMessage<T> newMessage();

	private void setupExecutorService() {
		if (mExecutor == null || mExecutor.isTerminated()) {
			mExecutor = mGetExecutorService.get();
		}
	}

	@Override
	public synchronized void start() {
		mLogger.info("starting Server.");
		setupExecutorService();
		mServerFuture = mExecutor.submit(this::run);
		mRunning = true;
	}

	@Override
	public synchronized void stop() {
		mLogger.info("stopping Server..");
		mRunning = false;
		try {
			mCancelled = true;
			mServerFuture.get(10, TimeUnit.SECONDS);
			mLogger.info("Server stopped.");
		} catch (InterruptedException | ExecutionException e) {
			mLogger.error("Server Thread was interrupted.", e);
		} catch (final TimeoutException e) {
			final boolean canceled = mServerFuture.cancel(true);
			mLogger.error(String.format("Server Thread Timed out. Canceled execution: %s", canceled));
		}
	}

	@Override
	public void setHelloMessage(final String helloMessage) {
		mHelloMessage = helloMessage;
	}

	private void run() {
		try {
			mSocket = new ServerSocket(mPort);
		} catch (final IOException e1) {
			mCancelled = true;
			mLogger.error("Server could not be started.", e1);
			return;
		}

		mTypeRegistry = getTypeRegistry();

		// use FutureClient set in constructor here.
		listen();
		while (true) {
			synchronized (this) {
				mClient = new FutureClient<T>(mLogger);
				mConnectionEvent.set();
			}
			listen();
		}
	}

	private void listen() {
		mClient.setRegistry(mTypeRegistry);
		mClient.setFactory(this::newMessage);

		try {
			mLogger.info("listening on port " + mPort);
			final Socket clientSocket = mSocket.accept();

			mLogger.info("accepted connection: " + clientSocket);
			mClient.setSocket(clientSocket);
			mLogger.info("setting hello message: " + mHelloMessage);
			mClient.setHelloMessage(getClass().getSimpleName(), mHelloMessage, Level.INFO);
			mLogger.info("setting executor");
			mClient.setExecutor(mExecutor);

			// send(Action.HELLO, null);
		} catch (final IOException e) {
			mLogger.error("Could not listen on port:" + mPort);
			mClient.cancel(true);
			return;
		}

		try {
			final Client<T> client = mClient.get(1, TimeUnit.MINUTES);

			client.finished().get();
		} catch (InterruptedException | ExecutionException e) {
			mLogger.error("Client", e);
			mClient.cancel(true);
			return;
		} catch (final TimeoutException e) {
			mLogger.error("Timed out waiting for Client");
			mClient.cancel(true);
			return;
		}
	}

	@Override
	public synchronized Client<T> waitForConnection(final long timeout, final TimeUnit timeunit)
			throws InterruptedException, ExecutionException, TimeoutException {
		if (!mRunning || mServerFuture.isDone()) {
			throw new IllegalStateException("Server not running.");
		}

		final Client<T> client = mClient.get(timeout, timeunit);
		mConnectionEvent.clear();
		return client;
	}

}