/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TreeAutomizer Plugin.
 *
 * The ULTIMATE TreeAutomizer Plugin is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TreeAutomizer Plugin is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TreeAutomizer Plugin. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TreeAutomizer Plugin, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TreeAutomizer Plugin grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.chc;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.ModernAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class HornAnnot extends ModernAnnotations {

	private static final long serialVersionUID = -3542578811318106167L;
	private static final String KEY = HornAnnot.class.getName();

	private final ManagedScript mBackendSolverScript;
	private final HcSymbolTable mSymbolTable;
	private final String mFileName;
	private final List<HornClause> mHornClauses;
	private final boolean mHasCheckSat;
	private final ChcCategoryInfo mChcCategoryInfo;

	/***
	 * An annotation of horn clauses.
	 *
	 * @param filename
	 * @param clauses
	 * @param backendSolver
	 * @param symbolTable
	 */
	public HornAnnot(final String filename, final ManagedScript backendSolver, final HcSymbolTable symbolTable,
			final List<HornClause> clauses, final boolean hasCheckSat, final ChcCategoryInfo chcCategoryInfo) {
		mFileName = filename;
		mHornClauses = clauses;
		mBackendSolverScript = backendSolver;
		mSymbolTable = symbolTable;
		mHasCheckSat = hasCheckSat;
		mChcCategoryInfo = chcCategoryInfo;
	}

	public ManagedScript getScript() {
		return mBackendSolverScript;
	}

	public HcSymbolTable getSymbolTable() {
		return mSymbolTable;
	}

	public List<HornClause> getHornClauses() {
		return mHornClauses;
	}

	/**
	 *
	 * @return true if a (check-sat) command occurred in the input smt script
	 */
	public boolean hasCheckSat() {
		return mHasCheckSat;
	}

	public String getFileName() {
		return mFileName;
	}

	@Override
	public String toString() {
		final StringBuilder res = new StringBuilder();
		res.append("(HornAnnot) List of HornClauses:").append(CoreUtil.getPlatformLineSeparator());
		for (final HornClause hc : mHornClauses) {
			res.append(hc.toString());
			res.append(CoreUtil.getPlatformLineSeparator());
		}
		return res.toString();
	}

	public void annotate(final IElement node) {
		node.getPayload().getAnnotations().put(KEY, this);
	}

	public static HornAnnot getAnnotation(final IElement node) {
		return ModelUtils.getAnnotation(node, KEY, a -> (HornAnnot) a);
	}

	@Override
	public IAnnotations merge(final IAnnotations other) {
		if (other instanceof HornAnnot) {
			throw new UnmergeableAnnotationsException("Not implemented for " + getClass().getName());
		}
		return super.merge(other);
	}

	public ChcCategoryInfo getChcCategoryInfo() {
		return mChcCategoryInfo;
	}
}
