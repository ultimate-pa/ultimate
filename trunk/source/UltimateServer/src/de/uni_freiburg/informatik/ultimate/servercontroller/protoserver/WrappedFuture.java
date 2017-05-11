package de.uni_freiburg.informatik.ultimate.servercontroller.protoserver;

import java.util.concurrent.CompletableFuture;

import com.google.protobuf.GeneratedMessageV3;

public class WrappedFuture<T extends GeneratedMessageV3> {
	public final CompletableFuture<T> future;
	public final Class<T> type;

	public WrappedFuture(final Class<T> wType) {
		this.future = new CompletableFuture<T>();
		this.type = wType;
	}
}
