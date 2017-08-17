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
package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.parsing;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HCSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.treeautomizer.HornUtilConstants;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class HornAnnot implements IAnnotations {

	private static final long serialVersionUID = -3542578811318106167L;
	private final ManagedScript mBackendSolverScript;
	private final Map<String, Object> mMaechtigUnnoetigBenannteMap = new HashMap<>();
	private final HCSymbolTable mSymbolTable;

	/***
	 * An annotation of horn clauses.
	 * @param clauses
	 * @param backendSolver
	 * @param symbolTable
	 */
	public HornAnnot(final List<HornClause> clauses, 
			final ManagedScript backendSolver,
			final HCSymbolTable symbolTable) {
		mMaechtigUnnoetigBenannteMap.put(HornUtilConstants.HORN_ANNOT_NAME, clauses);
		mBackendSolverScript = backendSolver;
		mSymbolTable = symbolTable;
	}

	@Override
	public Map<String, Object> getAnnotationsAsMap() {
		return mMaechtigUnnoetigBenannteMap;
	}

	public ManagedScript getScript() {
		return mBackendSolverScript;
	}
	
	public HCSymbolTable getSymbolTable() {
		return mSymbolTable;
	}
	@Override
	public String toString() {
		StringBuilder res = new StringBuilder();
		for (final Entry<String, Object> en : mMaechtigUnnoetigBenannteMap.entrySet()) {
			if (res.length() != 0) {
				res.append('\t');
			}
			res.append("{{" + en.getValue().toString() + "}}");
		}
		return res.toString();
	}
}
