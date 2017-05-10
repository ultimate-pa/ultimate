package de.uni_freiburg.informatik.ultimate.interactive;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.function.BiConsumer;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * {@link IWrappedMessage} is a message with a header that can be sent or
 * received by an {@link IServer}.
 * 
 * @author Julian Jarecki
 *
 */
public interface IWrappedMessage<T> {
	<D extends T> D get();

	String getUniqueDataTypeIdentifier();

	String getUniqueQueryDataTypeIdentifier();

	String getUniqueQueryIdentifier();

	Action getAction();

	Message getMessage();

	/**
	 * blocks until the message is read from input Stream.
	 * 
	 * @param input
	 * @throws IOException
	 * @throws InterruptedException
	 */
	void readFrom(InputStream input, ITypeRegistry<T> typeRegistry) throws IOException, InterruptedException;
	
	void writeTo(OutputStream output) throws IOException;

	Writer<T> writer();


	class Message {
		public final static String PRAEFIX_PATTERN = "[%s] %s";

		public final String source;
		public final String text;
		public final Level level;

		public Message(final String source, final String text, final Level level) {
			this.source = source;
			this.text = text;
			this.level = level;
		}

		public void log(final ILogger logger) {
			final String msg = String.format(PRAEFIX_PATTERN, source, text);
			level.logmethod.accept(logger, msg);
		}

		public void log(final ILogger logger, final String praefix) {
			final String msg = String.format(PRAEFIX_PATTERN, praefix + source, text);
			level.logmethod.accept(logger, msg);
		}

		public enum Level {
			DEBUG(ILogger::debug), INFO(ILogger::info), WARN(ILogger::warn), ERROR(ILogger::error);

			BiConsumer<ILogger, String> logmethod;

			Level(final BiConsumer<ILogger, String> logmethod) {
				this.logmethod = logmethod;
			}
		}
	}

	interface Writer<T> {
		Writer<T> setMessage(Message message);

		Writer<T> setAction(Action action);
		
		Writer<T> setQid(String qid);
		
		default Writer<T> answer(final IWrappedMessage<?> query) {
			return setQid(query.getUniqueQueryIdentifier());
		};

		Writer<T> setData(T data);

		Writer<T> setQuery(Class<? extends T> type);

		void write();
	}

	public enum Action {
		QUIT, // used to indicate that the connection will be terminated
		HELLO, // used for an initial message from Server to Client
		LOGGING, // Not data, just logging
		SEND, // sending data only (handle by reference)
		REQUEST, // request data, possibly also sending
		SORRY, // no data in response to a request
	}
}
