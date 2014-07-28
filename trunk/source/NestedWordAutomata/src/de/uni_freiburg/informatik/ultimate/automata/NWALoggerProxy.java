package de.uni_freiburg.informatik.ultimate.automata;

import java.util.Enumeration;
import java.util.ResourceBundle;

import org.apache.log4j.Appender;
import org.apache.log4j.Level;
import org.apache.log4j.Logger;
import org.apache.log4j.Priority;
import org.apache.log4j.spi.LoggerRepository;
import org.apache.log4j.spi.LoggingEvent;

/**
 * This class serves as proxy to enable a realtively painless transition from
 * UltimateServices to the new API.
 * 
 * It allows lazy loading of the logger at the cost of losing all logging that
 * happens before the plugin is live.
 * 
 * @author dietsch
 * 
 */
public class NWALoggerProxy extends Logger {

	private Logger mLogger;

	void setLogger(Logger logger) {
		mLogger = logger;
	}

	public NWALoggerProxy() {
		super("LoggerProxy");
	}

	protected NWALoggerProxy(String name) {
		super(name);
	}

	@Override
	public void trace(Object message) {
		if (mLogger != null) {
			mLogger.trace(message);
		}
	}

	@Override
	public void trace(Object message, Throwable t) {
		if (mLogger != null) {
			mLogger.trace(message, t);
		}
	}

	@Override
	public void debug(Object message) {
		if (mLogger != null) {
			mLogger.debug(message);
		}
	}

	@Override
	public void debug(Object message, Throwable t) {
		if (mLogger != null) {
			mLogger.debug(message, t);
		}
	}

	@Override
	public void info(Object message) {
		if (mLogger != null) {
			mLogger.info(message);
		}
	}

	@Override
	public void info(Object message, Throwable t) {
		if (mLogger != null) {
			mLogger.info(message, t);
		}
	}

	@Override
	public void warn(Object message) {
		if (mLogger != null) {
			mLogger.warn(message);
		}
	}

	@Override
	public void warn(Object message, Throwable t) {
		if (mLogger != null) {
			mLogger.warn(message, t);
		}
	}

	@Override
	public void error(Object message) {
		if (mLogger != null) {
			mLogger.error(message);
		}
	}

	@Override
	public void error(Object message, Throwable t) {
		if (mLogger != null) {
			mLogger.error(message, t);
		}
	}

	@Override
	public void fatal(Object message) {
		if (mLogger != null) {
			mLogger.fatal(message);
		}
	}

	@Override
	public void fatal(Object message, Throwable t) {
		if (mLogger != null) {
			mLogger.fatal(message, t);
		}
	}

	@Override
	public void log(Priority priority, Object message) {
		if (mLogger != null) {
			mLogger.log(priority, message);
		}
	}

	@Override
	public void log(Priority priority, Object message, Throwable t) {
		if (mLogger != null) {
			mLogger.log(priority, message, t);
		}
	}

	@Override
	public void log(String callerFQCN, Priority level, Object message, Throwable t) {
		if (mLogger != null) {
			mLogger.log(callerFQCN, level, message, t);
		}
	}

	@Override
	public synchronized void addAppender(Appender newAppender) {
		if (mLogger != null) {
			mLogger.addAppender(newAppender);
		}
	}

	@Override
	public void assertLog(boolean assertion, String msg) {
		if (mLogger != null) {
			mLogger.assertLog(assertion, msg);
		}
	}

	@Override
	public void callAppenders(LoggingEvent arg0) {
		if (mLogger != null) {
			mLogger.callAppenders(arg0);
		}
	}

	@Override
	public boolean getAdditivity() {
		if (mLogger != null) {
			return mLogger.getAdditivity();
		}
		return false;
	}

	@Override
	public synchronized Enumeration getAllAppenders() {
		if (mLogger != null) {
			return mLogger.getAllAppenders();
		}
		return null;
	}

	@Override
	public synchronized Appender getAppender(String name) {
		if (mLogger != null) {
			return mLogger.getAppender(name);
		}
		return null;

	}

	@Override
	public Priority getChainedPriority() {
		if (mLogger != null) {
			return mLogger.getChainedPriority();
		}
		return null;
	}

	@Override
	public Level getEffectiveLevel() {
		if (mLogger != null) {
			return mLogger.getEffectiveLevel();
		}
		return null;
	}

	@Override
	public LoggerRepository getHierarchy() {
		if (mLogger != null) {
			return mLogger.getHierarchy();
		}
		return null;
	}

	@Override
	public LoggerRepository getLoggerRepository() {
		if (mLogger != null) {
			return mLogger.getLoggerRepository();
		}
		return null;
	}

	@Override
	public ResourceBundle getResourceBundle() {
		if (mLogger != null) {
			return mLogger.getResourceBundle();
		}
		return null;
	}

	@Override
	public boolean isAttached(Appender appender) {
		if (mLogger != null) {
			return mLogger.isAttached(appender);
		}
		return false;
	}

	@Override
	public boolean isDebugEnabled() {
		if (mLogger != null) {
			return mLogger.isDebugEnabled();
		}
		return false;
	}

	@Override
	public boolean isEnabledFor(Priority level) {
		if (mLogger != null) {
			return mLogger.isEnabledFor(level);
		}
		return false;
	}

	@Override
	public boolean isInfoEnabled() {
		if (mLogger != null) {
			return mLogger.isInfoEnabled();
		}
		return false;
	}

	@Override
	public boolean isTraceEnabled() {
		if (mLogger != null) {
			return mLogger.isTraceEnabled();
		}
		return false;
	}

	@Override
	public void l7dlog(Priority arg0, String arg1, Object[] arg2, Throwable arg3) {
		if (mLogger != null) {
			mLogger.l7dlog(arg0, arg1, arg2, arg3);
		}
	}

	@Override
	public void l7dlog(Priority arg0, String arg1, Throwable arg2) {
		if (mLogger != null) {
			mLogger.l7dlog(arg0, arg1, arg2);
		}
	}

	@Override
	public synchronized void removeAllAppenders() {
		if (mLogger != null) {
			mLogger.removeAllAppenders();
		}
	}

	@Override
	public synchronized void removeAppender(Appender appender) {
		if (mLogger != null) {
			mLogger.removeAppender(appender);
		}
	}

	@Override
	public synchronized void removeAppender(String name) {
		if (mLogger != null) {
			mLogger.removeAppender(name);
		}
	}

	@Override
	public void setAdditivity(boolean additive) {
		if (mLogger != null) {
			mLogger.setAdditivity(additive);
		}
	}

	@Override
	public void setLevel(Level level) {
		if (mLogger != null) {
			mLogger.setLevel(level);
		}
	}

	@Override
	public void setPriority(Priority priority) {
		if (mLogger != null) {
			mLogger.setPriority(priority);
		}
	}

	@Override
	public void setResourceBundle(ResourceBundle bundle) {
		if (mLogger != null) {
			mLogger.setResourceBundle(bundle);
		}
	}

	@Override
	public String toString() {
		if (mLogger != null) {
			mLogger.toString();
		}
		return "Uninitialized";
	}
	
	

}
