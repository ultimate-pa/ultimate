/*
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CountertraceParser plug-in.
 *
 * The ULTIMATE CountertraceParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CountertraceParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CountertraceParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CountertraceParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CountertraceParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.countertrace.parser;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ObjectContainer;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pea.CounterTrace;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;

/**
 * ISource implementation that parses {@code .ct} (countertrace) files containing DC-phase notation as produced by
 * {@link CounterTrace#toString()}.
 *
 * <p>
 * Each line of a {@code .ct} file may be:
 * </p>
 * <ul>
 * <li>A variable/constant declaration (e.g., {@code Input R is bool}, {@code Const c is 5}), analogous to {@code .req}
 * files.</li>
 * <li>A countertrace, optionally preceded by an ID followed by a colon (e.g., {@code ID001: ⌈R⌉;true}). The
 * countertrace may be wrapped in ¬(...) (countertrace formulae) or be bare — both forms produce the same
 * {@link CounterTrace} object, as the ¬ is treated as a semantic annotation and ignored.</li>
 * </ul>
 * <p>
 * Empty lines and lines starting with {@code //} are skipped.
 * </p>
 *
 * <p>
 * Only countertraces without entry events and without forbidden events are supported.
 * </p>
 */
public class CountertraceParser implements ISource {
	private ILogger mLogger;
	private final List<String> mFileNames = new java.util.ArrayList<>();
	private IUltimateServiceProvider mServices;
	private CountertraceParserResultUtil mReporter;

	@Override
	public void init() {
		// not necessary
	}

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public File[] parseable(final File[] files) {
		final List<File> rtrList = Arrays.stream(files).filter(this::parseable).collect(Collectors.toList());
		return rtrList.toArray(new File[rtrList.size()]);
	}

	public boolean parseable(final File file) {
		return file.getName().endsWith(".ct");
	}

	@Override
	public IElement parseAST(final File[] files) throws Exception {
		final List<PatternType<?>> allPatterns = new ArrayList<>();
		for (final File file : files) {
			final String filePath = file.getAbsolutePath();
			mFileNames.add(filePath);
			mLogger.info("Parsing countertrace file " + filePath);
			try {
				final CountertraceFileResult result = CtParser.parseFile(mLogger, filePath);
				allPatterns.addAll(result.getDeclarations());
				for (final CountertraceParserResult ctr : result.getCountertraces()) {
					final String id = ctr.getId() != null ? ctr.getId() : "ct" + allPatterns.size();
					allPatterns.add(new CountertracePattern(id, ctr.getCounterTrace()));
				}
				mLogger.info("Parsed " + result.getCountertraces().size() + " countertrace entr(y/ies) and "
						+ result.getDeclarations().size() + " declaration(s) from " + filePath);
			} catch (final Exception ex) {
				mReporter.unexpectedParserFailure(filePath,
						String.format("%s: %s", ex.getClass().getSimpleName(), ex.getMessage()));
				throw ex;
			}
		}

		if (mReporter.isAlreadyAborted()) {
			return null;
		}

		return new ObjectContainer<>(allPatterns);
	}

	@Override
	public String[] getFileTypes() {
		return new String[] { ".ct" };
	}

	@Override
	public ModelType getOutputDefinition() {
		try {
			return new ModelType(getPluginID(), ModelType.Type.OTHER, mFileNames);
		} catch (final Exception ex) {
			mLogger.fatal("syntax error: " + ex.getMessage());
			return null;
		}
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mReporter = new CountertraceParserResultUtil(mLogger, mServices);
	}

	@Override
	public void finish() {
		// not necessary
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return null;
	}
}
