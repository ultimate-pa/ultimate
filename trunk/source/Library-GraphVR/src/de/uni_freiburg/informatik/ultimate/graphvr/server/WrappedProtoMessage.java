package de.uni_freiburg.informatik.ultimate.graphvr.server;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.graphvr.protobuf.Meta.Header;

public class WrappedProtoMessage {
	final public Header header;
	final public GeneratedMessageV3[] data;

	public WrappedProtoMessage(Header header, GeneratedMessageV3... data) {
		this.header = header;
		this.data = data;
	}
}
