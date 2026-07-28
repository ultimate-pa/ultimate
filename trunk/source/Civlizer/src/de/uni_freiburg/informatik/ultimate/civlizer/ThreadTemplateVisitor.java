/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE Civlizer plug-in.
 *
 * The ULTIMATE Civlizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Civlizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Civlizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Civlizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Civlizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.civlizer;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieUtils;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.JoinStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.WitnessInvariant;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;

/**
 * Visitor over a Boogie AST that extracts thread-related metadata, variable usage information and annotation data from
 * a program.
 *
 * <p>
 * This visitor builds several internal mappings while traversing a Boogie program, including:
 * <ul>
 * <li>Global and procedure-local variable usage per statement location</li>
 * <li>Procedure parameter usage derived from statements</li>
 * <li>Thread identifiers (TIDs) associated or used in thread template</li>
 * <li>Entry, exit, and final invariants extracted from witness annotations</li>
 * </ul>
 *
 * <p>
 * The collected information is later used by the Civlizer analysis pipeline to reason about concurrency structure and
 * thread associations.
 *
 * <p>
 * Thread identifiers are represented using {@link Tid}, and are tracked in association, usage, and global TID sets.
 */
final class ThreadTemplateVisitor extends BoogieVisitor {

	private final BoogieIcfgContainer mIcfg;
	private String mCurrentProcedure;

	private final Map<String, Expression> mEntryAnnotationMap = new HashMap<>();
	private final Map<String, Expression> mExitAnnotationMap = new HashMap<>();

	private final Map<String, List<Tid>> mAssociationTidMap = new HashMap<>();
	private final Map<String, List<Tid>> mUsedTidMap = new HashMap<>();
	private final Map<String, List<Tid>> mAllTidMap = new HashMap<>();
	private final Set<Tid> mTids;

	ThreadTemplateVisitor(final Unit boogieFile, final BoogieIcfgContainer icfg) {
		mIcfg = icfg;
		mCurrentProcedure = null;

		mTids = new HashSet<>();

		for (final Declaration elem : boogieFile.getDeclarations()) {
			processDeclaration(elem);
		}

		for (final String key : mAssociationTidMap.keySet()) {
			mAllTidMap.put(key, new ArrayList<>(mAssociationTidMap.get(key)));
		}

		for (final String key : mUsedTidMap.keySet()) {
			final List<Tid> tids = mAllTidMap.computeIfAbsent(key, k -> new ArrayList<>());

			for (final Tid tid : mUsedTidMap.get(key)) {
				if (!tids.contains(tid)) {
					tids.add(tid);
				}
			}
		}

		// remove duplicates per list
		for (final List<Tid> list : mAllTidMap.values()) {
			final Set<Tid> dedup = new LinkedHashSet<>(list);
			list.clear();
			list.addAll(dedup);
		}

		for (final List<Tid> tidList : mAllTidMap.values()) {
			mTids.addAll(tidList);
		}
	}

	Set<Tid> getTids() {
		return mTids;
	}

	Map<String, List<Tid>> getAssociationTidMap() {
		return mAssociationTidMap;
	}

	Map<String, List<Tid>> getUsedTidMap() {
		return mUsedTidMap;
	}

	Map<String, List<Tid>> getAllTidMap() {
		return mAllTidMap;
	}

	Map<String, Expression> getEntryAnnotationMap() {
		return mEntryAnnotationMap;
	}

	Map<String, Expression> getExitAnnotationMap() {
		return mExitAnnotationMap;
	}

	@Override
	protected void visit(final Procedure decl) {
		mCurrentProcedure = decl.getIdentifier();

		final var icfgEntryLoc = mIcfg.getProcedureEntryNodes().get(mCurrentProcedure);
		final Expression entryInvariant = (Expression) WitnessInvariant.getAnnotation(icfgEntryLoc).getInvariant();
		mEntryAnnotationMap.put(mCurrentProcedure, entryInvariant);

		final var icfgExitLoc = mIcfg.getProcedureExitNodes().get(mCurrentProcedure);
		final Expression exitInvariant = (Expression) WitnessInvariant.getAnnotation(icfgExitLoc).getInvariant();
		mExitAnnotationMap.put(mCurrentProcedure, exitInvariant);

		if (!mCurrentProcedure.equals(BoogieUtils.START_PROCEDURE)
				&& !mAssociationTidMap.containsKey(mCurrentProcedure)) {
			mAssociationTidMap.put(mCurrentProcedure, new ArrayList<>());
		}

		super.visit(decl);
	}

	@Override
	protected void visit(final ForkStatement statement) {
		final Tid tid = new Tid(statement.getThreadID());

		List<Tid> tids = mAssociationTidMap.computeIfAbsent(statement.getProcedureName(), x -> new ArrayList<>());
		if (!tids.contains(tid)) {
			tids.add(tid);
		}

		tids = mUsedTidMap.computeIfAbsent(mCurrentProcedure, x -> new ArrayList<>());
		if (!tids.contains(tid)) {
			tids.add(tid);
		}
	}

	@Override
	protected void visit(final JoinStatement statement) {
		final Tid tid = new Tid(statement.getThreadID());

		final List<Tid> tids = mUsedTidMap.computeIfAbsent(mCurrentProcedure, x -> new ArrayList<>());
		if (!tids.contains(tid)) {
			tids.add(tid);
		}
	}
}
