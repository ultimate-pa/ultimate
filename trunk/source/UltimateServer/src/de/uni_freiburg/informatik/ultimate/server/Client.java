package de.uni_freiburg.informatik.ultimate.server;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.Socket;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.server.IWrappedMessage.Action;
import de.uni_freiburg.informatik.ultimate.server.IWrappedMessage.Message;
import de.uni_freiburg.informatik.ultimate.server.exceptions.ClientSorryException;
import de.uni_freiburg.informatik.ultimate.servermodel.HandlerRegistry;
import de.uni_freiburg.informatik.ultimate.servermodel.IHandlerRegistry;
import de.uni_freiburg.informatik.ultimate.servermodel.ITypeRegistry;

/**
 * represents a Client or possibly Future-Client. (separate class?) a Client
 * that should implement the Ultimate Interactive protocol
 * 
 * @author Julian Jarecki
 *
 */
public abstract class Client<T> {

	protected final ILogger mLogger;

	Socket mSocket = null;

	MessageQueue<T> mQueue = null;

	protected CompletableFuture<Socket> mClientFuture = new CompletableFuture<>();
	protected CompletableFuture<Void> mHelloFuture = new CompletableFuture<>();
	protected int mCurrentRequestId = 0;

	private ITypeRegistry<T> mTypeRegistry;
	private IHandlerRegistry<T> mHandlerRegistry;

	Client(Socket connectionSocket, ILogger logger, ITypeRegistry<T> typeRegistry) {
		this(logger, typeRegistry);
		// this.mSocket = connectionSocket;
		setSocket(connectionSocket);
	}

	Client(ILogger logger, ITypeRegistry<T> typeRegistry) {
		mLogger = logger;

		mTypeRegistry = typeRegistry;
		mQueue = new MessageQueue<T>(logger);
		mHandlerRegistry = new HandlerRegistry<>(mTypeRegistry);
	}

	protected void handle(IWrappedMessage<T> msg) {
		// mLogger.debug("handleWrappged: " + wrapped.header.toString());
		final String queryId = msg.getUniqueQueryIdentifier();
		final String typeName = msg.getUniqueQueryDataTypeIdentifier();
		Message logmsg = msg.getMessage();
		logmsg.log(mLogger);

		T data = msg.get();
		Action action = msg.getAction();
		switch (action) {
		case LOGGING:
			//if (!typeName.isEmpty())
			//	log(data.toString(), logmsg.level);
			break;
		case SORRY:
			mLogger.error(new ClientSorryException(msg));
		case SEND:
			if (!mTypeRegistry.registered(typeName)) {
				mLogger.warn(String.format("received message with data of unregistered type %s", typeName));
				break;
			}
			// final RegisteredProtoType<?> wt = mTypeRegistry.get(typeName);
			// if (mExpectedData.containsKey(queryId)) {
			// final String wTypeName =
			// wrapped.get().getDescriptorForType().getFullName();
			// WrappedFuture<? extends GeneratedMessageV3> wf =
			// mExpectedData.get(queryId);
			// if (action == Action.SORRY) {
			// final ClientSorryException e = new ClientSorryException(wrapped);
			// wf.future.completeExceptionally(e);
			// } else if (!Objects.equals(typeName, wTypeName)) {
			// final String message = String.format("Expected %s, but client
			// responded with type %s.", wTypeName,
			// typeName);
			// final IllegalStateException e = new
			// IllegalStateException(message);
			// wf.future.completeExceptionally(e);
			// } else {
			// wf.future.complete(wrapped.get());
			// }
			// } else {
			// wt.consume(wrapped.get());
			// }
			break;
		case REQUEST:
			if (queryId != null) {
				mLogger.error("handling client queries is not implemented yet.");
			} else {
				mLogger.warn("ignoring request message that has no Query attached");
				//mLogger.warn(wrapped.header.toString());
			}
			break;
		case QUIT:
			break;
		case HELLO:
			mLogger.info("callign complete on completablefuture for hello: " + mHelloFuture.toString());
			mHelloFuture.complete(null);
			break;
		default:
			break;
		}
	};

	protected abstract IWrappedMessage<T> construct();

	public void setSocket(Socket socket) {
		if (!mClientFuture.complete(socket))
			throw new IllegalStateException("Socket had already been set");
	}

	public boolean isConnected() {
		return mSocket != null && mSocket.isConnected();
	}

	public void closeConnection() {
		try {
			mSocket.close();
			mSocket = null;
		} catch (IOException e) {
			mLogger.error("failed to shut down connection gracefully.", e);
			mSocket = null;
		}
	}

	public void startQueue(ExecutorService executor) {

		try {
			mSocket = mClientFuture.get();

			InputStream input = mSocket.getInputStream();
			OutputStream output = mSocket.getOutputStream();

			executor.submit(() -> runOutput(output));
			executor.submit(() -> runInput(input, mTypeRegistry));
			// ObjectInputStream inFromClient = new ObjectInputStream(input);
			// ObjectOutputStream outToClient = new
			// ObjectOutputStream(connectionSocket.getOutputStream());
			// serveRequest(inFromClient, outToClient);
			// outToClient.flush();

		} catch (IOException | InterruptedException | ExecutionException ex) {
			mLogger.info("Cannot initialize Client.");
		}
	}

	private void runOutput(OutputStream output) {
		IWrappedMessage<T> msg;
		while (true) {
			msg = mQueue.poll(5, TimeUnit.SECONDS);
			if (msg == null)
				continue;

			try {
				msg.writeTo(output);
			} catch (IOException e) {
				mLogger.error(e);
				continue;
			}
		}
	}

	private void runInput(InputStream input, ITypeRegistry<T> typeRegistry) {
		IWrappedMessage<T> msg;
		while (true) {
			try {
				msg = construct();
				if (msg == null) {
					mLogger.error("Queue created null message.");
					break;
				}
				msg.readFrom(input, typeRegistry);

				handle(msg);
			} catch (IOException e) {
				mLogger.error("failed to read input", e);
				return;
			} catch (InterruptedException e) {
				mLogger.error("input thread interrupted.", e);
				continue;
			}
		}
	}

}