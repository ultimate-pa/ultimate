package de.uni_freiburg.informatik.ultimate.server;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.Socket;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CompletionStage;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.TimeUnit;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.interactive.IHandlerRegistry;
import de.uni_freiburg.informatik.ultimate.interactive.ITypeRegistry;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage.Action;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage.Message;
import de.uni_freiburg.informatik.ultimate.interactive.exceptions.ClientSorryException;

/**
 * represents a Client or possibly Future-Client. (separate class?) a Client
 * that should implement the Ultimate Interactive protocol
 * 
 * @author Julian Jarecki
 *
 */
public abstract class Client<T> {

	protected final ILogger mLogger;

	protected final Socket mSocket;

	protected final MessageQueue<T> mQueue;

	protected CompletableFuture<Client<T>> mHelloFuture = new CompletableFuture<>();
	protected int mCurrentRequestId = 0;

	private ITypeRegistry<T> mTypeRegistry;
	private IHandlerRegistry<T> mHandlerRegistry;

	Client(Socket connectionSocket, ILogger logger, ITypeRegistry<T> typeRegistry) {
		mLogger = logger;

		mTypeRegistry = typeRegistry;
		mQueue = new MessageQueue<T>(logger);
		mHandlerRegistry = new HandlerRegistry<>(mTypeRegistry);
		mSocket = connectionSocket;
	}

	public CompletionStage<Client<T>> hasSaidHello() {
		return mHelloFuture;
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
			// if (!typeName.isEmpty())
			// log(data.toString(), logmsg.level);
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
				// mLogger.warn(wrapped.header.toString());
			}
			break;
		case QUIT:
			break;
		case HELLO:
			mLogger.info("callign complete on completablefuture for hello: " + mHelloFuture.toString());
			mHelloFuture.complete(this);
			break;
		default:
			break;
		}
	};

	protected abstract IWrappedMessage<T> construct();

	public void closeConnection() {
		try {
			mSocket.close();
		} catch (IOException e) {
			mLogger.error("failed to shut down connection gracefully.", e);
		}
	}

	public void startQueue(ExecutorService executor) throws IOException {
		InputStream input = mSocket.getInputStream();
		OutputStream output = mSocket.getOutputStream();

		executor.submit(() -> runOutput(output));
		executor.submit(() -> runInput(input, mTypeRegistry));
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