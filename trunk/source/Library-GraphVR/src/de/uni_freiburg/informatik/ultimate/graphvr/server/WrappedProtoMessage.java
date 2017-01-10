package de.uni_freiburg.informatik.ultimate.graphvr.server;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.graphvr.protobuf.Meta.Header;
import de.uni_freiburg.informatik.ultimate.graphvr.protobuf.Meta.Header.Action;

public class WrappedProtoMessage {
	final public Header header;
	final public GeneratedMessageV3 data;

	public static WrappedProtoMessage wrap(final GeneratedMessageV3 data) {
		final Header header = Header.newBuilder().setAction(Action.SEND).setDataType(data.getClass().getName()).build();
		return new WrappedProtoMessage(header, data);
	}

	public WrappedProtoMessage(Header header, GeneratedMessageV3 data) {
		this.header = header;
		this.data = data;
	}

	public <T extends GeneratedMessageV3> T get() {
		return (T) data;
	}
}
