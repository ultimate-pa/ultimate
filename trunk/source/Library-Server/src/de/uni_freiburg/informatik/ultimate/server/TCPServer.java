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

	public TCPServer(ILogger logger, int port) {
		mLogger = logger;
		mPort = port;
		mGetExecutorService = Executors::newWorkStealingPool;
		mClient = new FutureClient<T>(mLogger);
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
			// mClient.closeConnection();
			mClient.cancel(true);
			mServerFuture.get(10, TimeUnit.SECONDS);
			mLogger.info("Server stopped.");
		} catch (InterruptedException | ExecutionException e) {
			mLogger.error("Server Thread was interrupted.", e);
		} catch (TimeoutException e) {
			final boolean canceled = mServerFuture.cancel(true);
			mLogger.error(String.format("Server Thread Timed out. Canceled execution: %s", canceled));
		}
	}

	private void run() {
		try {
			mSocket = new ServerSocket(mPort);
		} catch (IOException e1) {
			mClient.cancel(true);
			mLogger.error("Server could not be started.", e1);
			return;
		}
		// mClient = new FutureClient<T>(mLogger);

		mClient.setRegistry(getTypeRegistry());
		mClient.setFactory(this::newMessage);

		// while (mRunning) {
		try {
			mLogger.info("listening on port " + mPort);
			Socket clientSocket = mSocket.accept();

			mLogger.info("accepted connection: " + clientSocket);
			mClient.setSocket(clientSocket);

			mClient.setExecutor(mExecutor);

			// send(Action.HELLO, null);
		} catch (IOException e) {
			mLogger.error("Could not listen on port:" + mPort);
			return;
		}

		try {
			Client<T> client = mClient.get(1, TimeUnit.MINUTES);

			client.finished().get();
		} catch (InterruptedException | ExecutionException e) {
			mLogger.error("Client", e);
			return;
		} catch (TimeoutException e) {
			mLogger.error("Timed out waiting for Client");
			return;
		}
	}

	@Override
	public Client<T> waitForConnection() throws InterruptedException, ExecutionException, TimeoutException {
		if (!mRunning || mServerFuture.isDone()) {
			throw new IllegalStateException("Server not running.");
		}

		return mClient.get(60, TimeUnit.SECONDS);
	}

}