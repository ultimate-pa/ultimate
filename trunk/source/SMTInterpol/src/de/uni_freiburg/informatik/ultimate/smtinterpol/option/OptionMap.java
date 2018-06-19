/*
 * Copyright (C) 2014 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.option;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.ParseEnvironment;

/**
 * A map to handle all options supported by SMTInterpol.  The map provides
 * general methods to set and get values for options based on the options name.
 * If the option is unknown, the methods will throw an
 * UnsupportedOperationException.
 *
 * The options are group into front end options and solver options.  The front
 * end options contain all options only used by the {@link ParseEnvironment}.
 * The solver options contain all options used by the solver whether created to
 * be used from command line or through its API.
 *
 * The diagnostic output channel option has a special role.  Since we are
 * working with {@link LogProxy}s, we might not be able to change the logging
 * destination.  Thus, only if the logger to be used is a {@link DefaultLogger},
 * we set up this option to change the log destination.  If a different logger
 * is used, we simply set up an option to print a warning if this option is
 * changed.
 *
 * The front end options are not activated by default.  All options are
 * available, but the option <pre>:regular-output-channel</pre> will print a
 * warning if its value is changed.  Only in the activated state, this option
 * actually changes the destination of the output.  To activate the front end
 * (if you actually use a {@link ParseEnvironment}), use the constructor
 * {@link #OptionMap(LogProxy, boolean)} with the second parameter set to
 * <code>true</code>.
 *
 * The map maintains a flag representing the current state of the solver.  If
 * this flag is turned on, all options that are not configured to be online
 * modifiable cannot be modified anymore.  Attempting to do so will throw a
 * {@link SMTLIBException}.
 * @author Juergen Christ
 */
public class OptionMap {

	private final static String DIAG_OUTPUT_CHANNEL_NAME =
		":diagnostic-output-channel";
	private final static String DIAG_OUTPUT_CHANNEL_DESC =
		"Where to print diagnostic output to.  Use \"stdout\" for standard "
			+ "output and \"stderr\" for standard error.";
	/**
	 * When copying this map, the options stored in this map can be either stay
	 * unchanged or be reset to their default value.  This is controlled by this
	 * enum.  The names are pretty self-expanatory.
	 * @author Juergen Christ
	 */
	public enum CopyMode {
		CURRENT_VALUE,
		RESET_TO_DEFAULT,
		/**
		 * Reset all options except for :regular-output-channel,
		 * :diagnostic-output-channel, and :verbosity.
		 */
		RESET_EXCEPT_CHANNELS
	}

	private final LinkedHashMap<String, Option> mOptions;
	private final LinkedHashMap<String, String> mAliases;
	private final SolverOptions mSolverOptions;
	private final FrontEndOptions mFrontEndOptions;
	private final LogProxy mLogger;
	private boolean mOnline;

	/**
	 * Convenience constructor for {@link #OptionMap(LogProxy, boolean)} where
	 * the front end is not activated by default.  This constructor should be
	 * used when the Java API of SMTInterpol is used.
	 * @param logger The logger to be used by SMTInterpol.
	 */
	public OptionMap(final LogProxy logger) {
		this(logger, false);
	}

	/**
	 * Create a new option map and set up the solver options.  If the logger
	 * given is a {@link DefaultLogger}, we also set up the option
	 * <code>:diagnostic-output-channel</code> to configure this logger.
	 * @param logger         The logger to be used by SMTInterpol.
	 * @param activeFrontEnd Activate the front end options?
	 */
	public OptionMap(final LogProxy logger, final boolean activeFrontEnd) {
		mOptions = new LinkedHashMap<String, Option>();
		mAliases = new LinkedHashMap<String, String>();
		mSolverOptions = new SolverOptions(this, logger);
		mLogger = logger;
		addOption(DIAG_OUTPUT_CHANNEL_NAME, new LoggerOption(
				DIAG_OUTPUT_CHANNEL_DESC, logger));
		mOnline = false;
		mFrontEndOptions = new FrontEndOptions(this, activeFrontEnd);
	}

	private OptionMap(final LogProxy logger, final LinkedHashMap<String, Option> options,
			final LinkedHashMap<String, String> aliases) {
		mOptions = options;
		mAliases = aliases;
		mSolverOptions = new SolverOptions(this);
		mFrontEndOptions = new FrontEndOptions(this);
		mLogger = logger;
		mOnline = false;
	}

	public void started() {
		for (final Option o : mOptions.values()) {
			o.started();
		}
	}

	/**
	 * Set the option map into online mode.  From now on, all options that are
	 * not online modifiable cannot be modified anymore.
	 */
	public void setOnline() {
		mOnline = true;
	}

	/**
	 * Get the logger used to construct this option map.
	 * @return The logger used to construct this option map.
	 */
	public final LogProxy getLogProxy() {
		return mLogger;
	}

	public final SolverOptions getSolverOptions() {
		return mSolverOptions;
	}

	public final FrontEndOptions getFrontEndOptions() {
		return mFrontEndOptions;
	}

	public void addOption(final String name, final Option option) {
		mOptions.put(name, option);
	}

	public void addAlias(final String name, final String alias) {
		mAliases.put(name, alias);
	}

	/**
	 * Get the current value of an option.  If the option is unknown to this
	 * option map, a <code>UnsupportedOperationException</code> will be thrown.
	 * @param option To option whose value should be retrieved.
	 * @return The current value of this option.
	 */
	public Object get(String option) {
		if (mAliases.containsKey(option)) {
			option = mAliases.get(option);
		}
		final Option o = mOptions.get(option);
		if (o == null) {
			throw new UnsupportedOperationException();
		}
		return o.get();
	}

	/**
	 * Set the value of an option.  The option map relies on the caller of this
	 * function to correctly
	 * @param option
	 * @param value
	 */
	public void set(String option, final Object value) {
		if (mAliases.containsKey(option)) {
			option = mAliases.get(option);
		}
		final Option o = mOptions.get(option);
		if (o == null) {
			throw new UnsupportedOperationException();
		}
		if (mOnline && !o.isOnlineModifiable()) {
			throw new SMTLIBException("Option " + option
					+ " can only be changed before setting the logic");
		}
		o.set(value);
	}

	/**
	 * Get all known option names.
	 * @return All known option names.
	 */
	public String[] getInfo() {
		final String[] res = new String[mOptions.size() + mAliases.size()];
		int pos = 0;
		for (final String opt : mOptions.keySet()) {
			res[pos++] = opt;
		}
		for (final String opt : mAliases.keySet()) {
			res[pos++] = opt;
		}
		return res;
	}

	/**
	 * Get information about a specific option.  The information contains the
	 * description, the default value, and the online modifiable state of this
	 * option.  If the option is unknown, an
	 * <code>UnsupportedOperationException</code> will be thrown.
	 * @param option The option to get information for.
	 * @return Information for this option.
	 */
	public Object[] getInfo(String option) {
		if (mAliases.containsKey(option)) {
			option = mAliases.get(option);
		}
		final Option o = mOptions.get(option);
		if (o == null) {
			throw new UnsupportedOperationException();
		}
		final ArrayList<Object> result = new ArrayList<Object>();
		result.add(":description");
		result.add(new QuotedObject(o.getDescription()));
		result.add(":default");
		result.add(o.defaultValue());
		if (o.isOnlineModifiable()) {
			result.add(":online-modifiable");
		}
		return result.toArray();
	}

	/**
	 * Reset every option to its default value and set the map back to offline
	 * state.
	 */
	public void reset() {
		mOnline = false;
		for (final Option o : mOptions.values()) {
			o.reset();
		}
	}

	public OptionMap copy(final CopyMode mode) {
		final LinkedHashMap<String, Option> options = new LinkedHashMap<String, Option>();
		for (final Map.Entry<String, Option> me : mOptions.entrySet()) {
			final Option cpy = me.getValue().copy();
			switch(mode) {
			case CURRENT_VALUE:
				break;
			case RESET_EXCEPT_CHANNELS:
				if (cpy instanceof VerbosityOption || cpy instanceof ChannelOption) {
					break;
				}
				// $FALL-THROUGH$
			default:
				cpy.reset();
			}
			options.put(me.getKey(), cpy);
		}
		return new OptionMap(mLogger, options, new LinkedHashMap<String, String>(mAliases));
	}

	Option getOption(final String key) {
		return mOptions.get(key);
	}
}
