package de.uni_freiburg.informatik.ultimate.servercontroller.protoserver;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.interactive.IRegisteredType;
import de.uni_freiburg.informatik.ultimate.interactive.ITypeRegistry;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage.Message.Level;
import de.uni_freiburg.informatik.ultimate.interactive.exceptions.UnregisteredTypeException;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Meta;
import de.uni_freiburg.informatik.ultimate.servercontroller.protobuf.Meta.Header;

public class WrappedProtoMessage implements IWrappedMessage<GeneratedMessageV3> {
	private static final String REQUEST_ID_PATTERN = "Request%s";
	private static int REQ_ID_COUNTER = 0;

	private Header header;
	private GeneratedMessageV3 data;
	private final ITypeRegistry<GeneratedMessageV3> mTypeRegistry;

	public WrappedProtoMessage(final ITypeRegistry<GeneratedMessageV3> typeRegistry) {
		mTypeRegistry = typeRegistry;
	}

	@SuppressWarnings("unchecked")
	@Override
	public <T extends GeneratedMessageV3> T get() {
		return (T) data;
	}

	@Override
	public String getUniqueDataTypeIdentifier() {
		return header.getDataType();
	}

	@Override
	public String getUniqueQueryDataTypeIdentifier() {
		return header.getQueryType();
	}

	@Override
	public String getUniqueQueryIdentifier() {
		return header.getQueryId();
	}

	@Override
	public IWrappedMessage.Action getAction() {
		return IWrappedMessage.Action.valueOf(header.getAction().name());
	}

	@Override
	public IWrappedMessage.Message getMessage() {
		final Meta.Message msg = header.getMessage();
		return new Message(msg.getSource(), msg.getText(), Level.valueOf(msg.getLevel().name()));
	}

	@Override
	public void writeTo(final OutputStream output) throws IOException {
		if (header == null) {
			throw new IllegalStateException("Missing Header");
		}

		header.writeDelimitedTo(output);

		if (data != null) {
			data.writeDelimitedTo(output);
		}
	}

	@Override
	public void readFrom(final InputStream input, final ITypeRegistry<GeneratedMessageV3> typeRegistry)
			throws IOException, InterruptedException {
		header = Header.parseDelimitedFrom(input);

		if (header == null)
			throw new IllegalStateException("Couldn't parse message Header");

		final String type = header.getDataType();

		if (type.isEmpty()) {
			data = null;
		} else if (typeRegistry.registered(type)) {
			data = typeRegistry.get(type).getDefaultInstance().getParserForType().parseDelimitedFrom(input);
		} else {
			final String errMsg = String.format("received unregistered message type: %s", type);
			throw new IllegalAccessError(errMsg);
		}

	}

	private String makeRequestId() {
		return String.format(REQUEST_ID_PATTERN, REQ_ID_COUNTER++);
	}

	@Override
	public Writer<GeneratedMessageV3> writer() {
		final WrappedProtoMessage me = this;
		final Header.Builder builder = Header.newBuilder();

		return new Writer<GeneratedMessageV3>() {
			GeneratedMessageV3 mData;

			@Override
			public Writer<GeneratedMessageV3> setMessage(final IWrappedMessage.Message message) {
				final Meta.Message.Builder mb = Meta.Message.newBuilder();
				mb.setLevel(Meta.Message.Level.valueOf(message.level.toString()));
				mb.setSource(message.source).setText(message.text);
				builder.setMessage(mb);
				return this;
			}

			@Override
			public Writer<GeneratedMessageV3> setAction(final IWrappedMessage.Action action) {
				builder.setAction(Header.Action.valueOf(action.toString()));
				return this;
			}

			@Override
			public Writer<GeneratedMessageV3> setData(final GeneratedMessageV3 data) {
				final Class<? extends GeneratedMessageV3> dType = data.getClass();
				final IRegisteredType<? extends GeneratedMessageV3> rType = mTypeRegistry.get(dType);
				if (rType == null)
					throw new UnregisteredTypeException(dType);
				builder.setDataType(rType.registeredName());
				mData = data;
				return this;
			}

			@Override
			public Writer<GeneratedMessageV3> setQuery(final Class<? extends GeneratedMessageV3> type) {
				final IRegisteredType<? extends GeneratedMessageV3> rType = mTypeRegistry.get(type);
				builder.setQueryType(rType.registeredName());
				builder.setQueryId(makeRequestId());
				return this;
			}

			@Override
			public Writer<GeneratedMessageV3> setQid(final String qid) {
				builder.setQueryId(qid);
				return this;
			}

			@Override
			public void write() {
				me.header = builder.build();
				me.data = mData;
			}
		};
	};
}
