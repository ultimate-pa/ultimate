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
 * Visitor over a Boogie AST that extracts thread-related metadata and witness annotations.
 *
 * <p>
 * For each procedure, this visitor collects:
 * <ul>
 * <li>TIDs associated with the procedure when it is forked</li>
 * <li>TIDs used by the procedure in fork and join statements</li>
 * <li>The union of associated and used TIDs</li>
 * <li>Entry and exit witness invariants</li>
 * </ul>
 *
 * <p>
 * TIDs are represented by {@link Tid}.
 */
final class ThreadTemplateVisitor extends BoogieVisitor {

	private final BoogieIcfgContainer mIcfg;

	private final Map<String, Expression> mEntryAnnotationMap = new HashMap<>();
	private final Map<String, Expression> mExitAnnotationMap = new HashMap<>();

	private final Map<String, List<Tid>> mAssociationTidMap = new HashMap<>();
	private final Map<String, List<Tid>> mUsedTidMap = new HashMap<>();
	private final Map<String, List<Tid>> mAllTidMap = new HashMap<>();

	private final Set<Tid> mTids = new LinkedHashSet<>();

	private String mCurrentProcedure;

	ThreadTemplateVisitor(final Unit boogieFile, final BoogieIcfgContainer icfg) {
		mIcfg = icfg;

		for (final Declaration declaration : boogieFile.getDeclarations()) {
			processDeclaration(declaration);
		}

		buildAllTidMap();
	}

	/**
	 * Returns all TIDs occurring in the thread template.
	 */
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
	protected void visit(final Procedure procedure) {
		mCurrentProcedure = procedure.getIdentifier();

		collectProcedureAnnotations(procedure);

		// Every non-start procedure is guaranteed to have an entry in the
		// association map, even if it is never forked.
		if (!BoogieUtils.START_PROCEDURE.equals(mCurrentProcedure)) {
			mAssociationTidMap.computeIfAbsent(mCurrentProcedure, key -> new ArrayList<>());
		}

		super.visit(procedure);
	}

	@Override
	protected void visit(final ForkStatement statement) {
		final Tid tid = new Tid(statement.getThreadID());

		addTid(mAssociationTidMap, statement.getProcedureName(), tid);
		addTid(mUsedTidMap, mCurrentProcedure, tid);
	}

	@Override
	protected void visit(final JoinStatement statement) {
		final Tid tid = new Tid(statement.getThreadID());

		addTid(mUsedTidMap, mCurrentProcedure, tid);
	}

	private void collectProcedureAnnotations(final Procedure procedure) {
		final String procedureName = procedure.getIdentifier();

		final var entryNode = mIcfg.getProcedureEntryNodes().get(procedureName);
		final var entryAnnotation = WitnessInvariant.getAnnotation(entryNode);
		if (entryAnnotation != null) {
			mEntryAnnotationMap.put(procedureName, (Expression) entryAnnotation.getInvariant());
		}

		final var exitNode = mIcfg.getProcedureExitNodes().get(procedureName);
		final var exitAnnotation = WitnessInvariant.getAnnotation(exitNode);
		if (exitAnnotation != null) {
			mExitAnnotationMap.put(procedureName, (Expression) exitAnnotation.getInvariant());
		}
	}

	private static void addTid(final Map<String, List<Tid>> tidMap, final String key, final Tid tid) {
		tidMap.computeIfAbsent(key, ignored -> new ArrayList<>()).add(tid);
	}

	private void buildAllTidMap() {
		for (final String procedure : mAssociationTidMap.keySet()) {
			mAllTidMap.put(procedure, new ArrayList<>(mAssociationTidMap.get(procedure)));
		}

		for (final var entry : mUsedTidMap.entrySet()) {
			final List<Tid> allTids = mAllTidMap.computeIfAbsent(entry.getKey(), ignored -> new ArrayList<>());

			for (final Tid tid : entry.getValue()) {
				if (!allTids.contains(tid)) {
					allTids.add(tid);
				}
			}
		}

		// Preserve insertion order while removing duplicates.
		for (final List<Tid> tids : mAllTidMap.values()) {
			final Set<Tid> uniqueTids = new LinkedHashSet<>(tids);
			tids.clear();
			tids.addAll(uniqueTids);
			mTids.addAll(uniqueTids);
		}
	}
}
