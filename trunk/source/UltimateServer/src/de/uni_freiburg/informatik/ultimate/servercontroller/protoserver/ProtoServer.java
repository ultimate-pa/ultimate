package de.uni_freiburg.informatik.ultimate.servercontroller.protoserver;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.interactive.ITypeRegistry;
import de.uni_freiburg.informatik.ultimate.interactive.IWrappedMessage;
import de.uni_freiburg.informatik.ultimate.server.TCPServer;

public class ProtoServer extends TCPServer<GeneratedMessageV3> {
	protected final ITypeRegistry<GeneratedMessageV3> mTypeRegistry = new ProtoTypeRegistry();

	public ProtoServer(final ILogger logger, final int port) {
		super(logger, port);
	}

	@Override
	public ITypeRegistry<GeneratedMessageV3> getTypeRegistry() {
		return mTypeRegistry;
	}

	@Override
	public IWrappedMessage<GeneratedMessageV3> newMessage() {
		return new WrappedProtoMessage(mTypeRegistry);
	}

}
