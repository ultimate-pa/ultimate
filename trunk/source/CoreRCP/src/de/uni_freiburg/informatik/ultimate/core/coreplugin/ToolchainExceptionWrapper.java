package de.uni_freiburg.informatik.ultimate.core.coreplugin;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class ToolchainExceptionWrapper extends Throwable {

	private static final long serialVersionUID = 4879856463210906523L;

	private final Throwable mRealReason;
	private final String mPluginId;

	ToolchainExceptionWrapper(String pluginId, Throwable t) {
		mPluginId = pluginId;
		mRealReason = t;
	}

	@Override
	public String toString() {
		return mPluginId + ": " + mRealReason.toString();
	}

	public Throwable getWrappedThrowable() {
		return mRealReason;
	}

	public String getPluginId() {
		return mPluginId;
	}

}
