package de.uni_freiburg.informatik.ultimate.server.protobuf;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.server.IWrappedMessage;
import de.uni_freiburg.informatik.ultimate.server.IWrappedMessage.Message.Level;
import de.uni_freiburg.informatik.ultimate.server.protobuf.Meta.Header;
import de.uni_freiburg.informatik.ultimate.servermodel.ITypeRegistry;

public class WrappedProtoMessage implements IWrappedMessage<GeneratedMessageV3> {
	private Header header;
	private GeneratedMessageV3 data;

	public static WrappedProtoMessage wrap(final GeneratedMessageV3 data) {
		final Header header = Header.newBuilder().setAction(Header.Action.SEND).setDataType(data.getClass().getName())
				.build();
		return new WrappedProtoMessage(header, data);
	}

	public WrappedProtoMessage(Header header, GeneratedMessageV3 data) {
		this.header = header;
		this.data = data;
	}

	public WrappedProtoMessage() {
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
	public void writeTo(OutputStream output) throws IOException {
		if (header == null) {
			throw new IllegalStateException("Missing Header");
		}

		header.writeDelimitedTo(output);

		if (data != null) {
			data.writeDelimitedTo(output);
		}
	}

	@Override
	public void readFrom(InputStream input, ITypeRegistry<GeneratedMessageV3> typeRegistry)
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
			throw new IllegalAccessError(String.format("received unregistered message type: %s", type));
		}

	}
}
