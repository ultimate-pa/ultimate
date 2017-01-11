package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.graphvr.server.IProtoServer;
import de.uni_freiburg.informatik.ultimate.graphvr.server.TCPServer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interactive.protobuf.TraceAbstractionProtos;

public class Server {

	private static IProtoServer mServer;

	public static void init(IUltimateServiceProvider services) {
		if (mServer == null) {
			mServer = new TCPServer(services.getLoggingService().getLogger(Activator.PLUGIN_ID), 6789);
			mServer.register(TraceAbstractionProtos.NestedWordAutomaton.class);
			mServer.register(TraceAbstractionProtos.TAPreferences.class);
			mServer.register(TraceAbstractionProtos.IterationInfo.class);
			mServer.register(TraceAbstractionProtos.CegarResult.class);
		}
	}

	public static IProtoServer get() {
		return mServer;
	}
}
