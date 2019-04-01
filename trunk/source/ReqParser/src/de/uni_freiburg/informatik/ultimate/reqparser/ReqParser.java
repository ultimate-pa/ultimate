/*
 * Copyright (C) 2013-2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ReqParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ReqParer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.reqparser;

import java.io.File;
import java.io.FileInputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import com.github.jhoenicke.javacup.runtime.Symbol;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ObjectContainer;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;
import de.uni_freiburg.informatik.ultimate.core.model.ISource;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.InitializationPattern;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

public class ReqParser implements ISource {
	private ILogger mLogger;
	private final List<String> mFileNames = new ArrayList<>();
	private IUltimateServiceProvider mServices;
	private ReqParserResultUtil mReporter;

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
		return file.getName().endsWith(".req");
	}

	@Override
	public IElement parseAST(final File[] files) throws Exception {
		final List<PatternType> rawPatterns = new ArrayList<>();
		for (final File file : files) {
			final String filePath = file.getAbsolutePath();
			mLogger.info("Parsing file " + filePath);
			try {
				final List<PatternType> pattern = parseFile(filePath);
				final List<PatternType> nonNullPatterns =
						pattern.stream().filter(a -> a != null).collect(Collectors.toList());
				if (nonNullPatterns.size() != pattern.size()) {
					mReporter.unexpectedParserFailure(filePath);
				}
				rawPatterns.addAll(nonNullPatterns);
			} catch (final Exception ex) {
				mReporter.unexpectedParserFailure(filePath);
				throw ex;
			}
		}

		if (mReporter.isAlreadyAborted()) {
			return null;
		}
		logPatternSize(rawPatterns, "in total");
		final List<PatternType> unifiedPatterns = unify(rawPatterns);
		logPatternSize(unifiedPatterns, "after unification");

		return new ObjectContainer<>(unifiedPatterns);
	}

	private List<PatternType> parseFile(final String reqFileName) throws Exception {
		final FileInputStream fis = new FileInputStream(reqFileName);
		try {
			final de.uni_freiburg.informatik.ultimate.lib.srparse.ReqParser parser =
					new de.uni_freiburg.informatik.ultimate.lib.srparse.ReqParser(mServices, mLogger, fis, reqFileName);
			final Symbol goal = parser.parse();
			final PatternType[] patterns = (PatternType[]) goal.value;
			return Arrays.asList(patterns);
		} finally {
			fis.close();
		}
	}

	private void logPatternSize(final List<PatternType> patterns, final String suffix) {
		final long patternWithId = patterns.stream().filter(a -> !(a instanceof InitializationPattern)).count();
		if (suffix == null) {
			mLogger.info(String.format("%s requirements (%s non-initialization)", patterns.size(), patternWithId));
		} else {
			mLogger.info(String.format("%s requirements (%s non-initialization) %s", patterns.size(), patternWithId,
					suffix));
		}
	}

	private List<PatternType> unify(final List<PatternType> patterns) {
		final List<PatternType> rtr = new ArrayList<>();
		final List<InitializationPattern> init = patterns.stream().filter(a -> a instanceof InitializationPattern)
				.map(a -> (InitializationPattern) a).collect(Collectors.toList());
		final UnionFind<InitializationPattern> uf = createUnionFind(init);
		checkTypeConflicts(uf.getAllRepresentatives());
		rtr.addAll(merge(uf));

		final List<PatternType> reqs = patterns.stream().filter(a -> a != null && !(a instanceof InitializationPattern))
				.collect(Collectors.toList());
		if (reqs.isEmpty()) {
			return rtr;
		}
		final UnionFind<PatternType> ufreq = createUnionFind(reqs);
		rtr.addAll(merge(ufreq));

		return rtr;
	}

	private void checkTypeConflicts(final Collection<InitializationPattern> inits) {
		final Map<String, InitializationPattern> seen = new HashMap<>();
		for (final InitializationPattern init : inits) {
			final InitializationPattern otherInit = seen.put(init.getId(), init);
			if (otherInit == null) {
				continue;
			}
			if (!Objects.equals(init.getType(), otherInit.getType())) {
				mReporter.unsupportedSyntaxError(new DummyLocation(),
						String.format("The initialization patterns %s and %s have conflicting types: %s vs. %s",
								init.getId(), otherInit.getId(), init.getType(), otherInit.getType()));
			}
		}
	}

	private List<PatternType> merge(final UnionFind<? extends PatternType> ufreq) {
		final List<PatternType> rtr = new ArrayList<>();
		for (final Set<? extends PatternType> eqclass : ufreq.getAllEquivalenceClasses()) {
			if (eqclass.size() == 1) {
				rtr.addAll(eqclass);
				continue;
			}
			mReporter.mergedRequirements(eqclass);
			rtr.add(merge(eqclass));
		}
		return rtr;
	}

	/**
	 * Create a new pattern from a set of patterns by concatenating their ids.
	 */
	private static PatternType merge(final Set<? extends PatternType> eqclass) {
		assert eqclass != null && eqclass.size() > 1;
		final StringBuilder newName = new StringBuilder();
		final Iterator<? extends PatternType> iter = eqclass.iterator();

		PatternType current = iter.next();
		final Class<?> last = current.getClass();
		newName.append(current.getId());
		while (iter.hasNext()) {
			current = iter.next();
			if (last != current.getClass()) {
				throw new AssertionError("Patterns with different types are assumed to be equivalent");
			}
			newName.append('_').append(current.getId());
		}
		return current.rename(newName.toString());
	}

	private <T extends PatternType> UnionFind<T> createUnionFind(final List<T> patterns) {
		final UnionFind<T> uf = new UnionFind<>();
		for (final T pattern : patterns) {
			final T rep = uf.findAndConstructEquivalenceClassIfNeeded(pattern);
			if (rep != pattern) {
				mReporter.mergedRequirements(pattern, rep);
			}
		}
		return uf;
	}

	@Override
	public String[] getFileTypes() {
		return new String[] { ".req" };
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
	public void setToolchainStorage(final IToolchainStorage storage) {
		// storage not needed
	}

	@Override
	public void setServices(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mReporter = new ReqParserResultUtil(mLogger, mServices);
	}

	@Override
	public void finish() {
		// not necessary
	}

	@Override
	public IPreferenceInitializer getPreferences() {
		return null;
	}

	private static final class DummyLocation extends DefaultLocation {

		private static final long serialVersionUID = 1L;

		public DummyLocation() {
			super("", -1, 0, 0, 0);
		}
	}

}
