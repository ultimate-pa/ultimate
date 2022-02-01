/*
 * Copyright (C) 2015-2016 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgStatementExtractor;

/**
 * Utility for grouping multiple subsequent havoc statements into a single havoc statement. Transformations are cached.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class HavocBundler {

	/** Used to extract statements from code blocks. */
	private final RcfgStatementExtractor mStatementExtractor;

	/**
	 * Cache of already processed code blocks and their versions with grouped havoc statements. Code blocks that are not
	 * present as a map key were never processed.
	 */
	private final Map<IcfgEdge, List<Statement>> mCache;

	/** Construct a new HavocBundler. */
	public HavocBundler() {
		mStatementExtractor = new RcfgStatementExtractor();
		mCache = new HashMap<>();
	}

	/**
	 * Extracts statements from a code block and groups subsequent havoc statements into a single havoc statement.
	 * <p>
	 * The result of the transformation is cached.
	 *
	 * @param block
	 *            Code block to be transformed.
	 * @return Extracted statements from the code block with grouped havoc statements
	 */
	public List<Statement> bundleHavocsCached(final IcfgEdge block) {
		// IcfgEdge is used as parameter, because IcfgEdge does not overwrite equals => faster map access
		List<Statement> cachedResult = mCache.get(block);
		if (cachedResult == null) {
			cachedResult = bundleHavocs(mStatementExtractor.process(block));
			mCache.put(block, cachedResult);
		}
		return cachedResult;
	}

	/** Internal, non-cached version of {@link #bundleHavocsCached(IcfgEdge)}. */
	private List<Statement> bundleHavocs(final List<Statement> block) {
		final List<Statement> result = new ArrayList<>(block.size());
		final List<HavocStatement> successiveHavocs = new ArrayList<>(block.size());
		for (final Statement stmt : block) {
			if (stmt instanceof HavocStatement) {
				successiveHavocs.add((HavocStatement) stmt);
			} else {
				if (!successiveHavocs.isEmpty()) {
					result.add(joinHavocs(successiveHavocs));
					successiveHavocs.clear();
				}
				result.add(stmt);
			}
		}
		if (!successiveHavocs.isEmpty()) {
			result.add(joinHavocs(successiveHavocs));
		}
		return result;
	}

	/**
	 * Creates a single havoc statement, that has the same effect as a list of subsequent havoc statements.
	 * 
	 * @param successiveHavocs
	 *            List of successive havoc statements.
	 * @return Single havoc statement
	 */
	private HavocStatement joinHavocs(final List<HavocStatement> successiveHavocs) {
		if (successiveHavocs.size() == 1) {
			return successiveHavocs.get(0); // avoid unnecessary creation of an equal statement object
		}
		final List<VariableLHS> vars = new ArrayList<>();
		for (final HavocStatement havocStmt : successiveHavocs) {
			for (final VariableLHS var : havocStmt.getIdentifiers()) {
				vars.add(var);
			}
		}
		final VariableLHS[] joinedVariables = vars.toArray(new VariableLHS[vars.size()]);
		final ILocation location = successiveHavocs.isEmpty() ? null : successiveHavocs.get(0).getLocation();
		return new HavocStatement(location, joinedVariables);
	}
}
