package de.uni_freiburg.informatik.ultimate.result;

import de.uni_freiburg.informatik.ultimate.core.coreplugin.ToolchainExceptionWrapper;

/**
 * IResult that is reported if toolchain has thrown a Throwable (Error or
 * Exception). The Throwable stored in the result has to be the Throwable that
 * was thrown by the toolchain.
 * 
 * @author Matthias Heizmann
 */
public class ExceptionOrErrorResult extends AbstractResult {
	private final Throwable m_Throwable;

	public ExceptionOrErrorResult(String plugin, Throwable throwable) {
		super(getPluginName(plugin, throwable));
		if (throwable instanceof ToolchainExceptionWrapper) {
			m_Throwable = ((ToolchainExceptionWrapper) throwable).getWrappedThrowable();
		} else {
			m_Throwable = throwable;
		}
	}

	private static String getPluginName(String plugin, Throwable throwable) {
		if (throwable instanceof ToolchainExceptionWrapper) {
			return ((ToolchainExceptionWrapper) throwable).getPluginId();
		} else {
			return plugin;
		}
	}

	@Override
	public String getShortDescription() {
		return m_Throwable.getClass().getSimpleName() + ": " + m_Throwable.getMessage();
	}

	@Override
	public String getLongDescription() {
		StackTraceElement[] stacktrace = m_Throwable.getStackTrace();
		String rtr = getPlugin() + ": " + getShortDescription();
		if (stacktrace != null && stacktrace.length > 0) {
			rtr = rtr + ": " + stacktrace[0].toString();
		}
		return rtr;
	}

	@Override
	public String toString() {
		return getLongDescription();
	}
}
