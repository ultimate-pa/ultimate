package de.uni_freiburg.informatik.ultimate.interactive.traceabstraction;

import com.google.protobuf.GeneratedMessageV3;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.interactive.IHandlerRegistry;

public class Server {

	private static IHandlerRegistry<GeneratedMessageV3> mServer;

	public static void init(IUltimateServiceProvider services) {
		if (mServer == null) {
			/*
			mServer = new TCPServer(services.getLoggingService().getLogger(Activator.PLUGIN_ID), 6789);
			mServer.register(TraceAbstractionProtos.NestedWordAutomaton.class);
			mServer.register(TraceAbstractionProtos.TAPreferences.class);
			mServer.register(TraceAbstractionProtos.IterationInfo.class);
			mServer.register(TraceAbstractionProtos.CegarResult.class);
			mServer.register(TraceAbstractionProtos.Question.class);
			*/
		}
	}

	public static IHandlerRegistry<GeneratedMessageV3> get() {
		return mServer;
	}
}
