/*
 * Joogie translates Java bytecode to the Boogie intermediate verification language
 * Copyright (C) 2011 Martin Schaef and Stephan Arlt
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */

package org.joogie.soot.helper;

import java.util.ArrayList;
import java.util.HashSet;

import org.joogie.HeapMode;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.boogie.expressions.Variable;
import org.joogie.boogie.types.BoogieBaseTypes;
import org.joogie.boogie.types.BoogieType;
import org.joogie.boogie.types.RefArrayType;
import org.joogie.util.Log;

import soot.ArrayType;
import soot.Body;
import soot.RefType;
import soot.SootClass;
import soot.SootMethod;
import soot.Trap;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewMultiArrayExpr;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.ThrowStmt;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;

/**
 * @author schaef
 */
public class BoogieExceptionAnalysis {

	private final BoogieProgramConstructionDecorator mProgDecl;

	BoogieExceptionAnalysis(BoogieProgramConstructionDecorator progDecl) {
		mProgDecl = progDecl;
	}

	public void addUncaughtExceptionsAndModifiesClause(SootMethod m, HashSet<SootMethod> visited, HeapMode heapmode) {
		visited.add(m);
		if (!m.hasActiveBody()) {
			for (SootClass c : m.getExceptions()) {
				BoogieProcedure proc = mProgDecl.getCache().lookupProcedure(m, heapmode);
				mProgDecl.getCache().getProcedureInfo(proc)
						.addUncaughtException(mProgDecl.getTypeFactory().lookupBoogieType(c.getType()));
			}
			return;
		}

		// recompute the possible exceptions (more precisely)
		// m.setExceptions(new ArrayList<SootClass>());
		Body b = m.getActiveBody();
		// TODO not sure if this it the right type
		ExceptionalUnitGraph tug = new ExceptionalUnitGraph(b);
		BoogieProcedure proc = mProgDecl.getCache().lookupProcedure(m, heapmode);

		for (Unit u : b.getUnits()) {

			if (u instanceof ThrowStmt) {
				ThrowStmt st = (ThrowStmt) u;
				if (st.getOp().getType() instanceof RefType) {
					RefType rt = (RefType) st.getOp().getType();
					Trap catchblock = findCatchBlock(st, rt.getSootClass(), tug);
					if (catchblock == null) {
						m.addExceptionIfAbsent(rt.getSootClass());
						mProgDecl.getCache().getProcedureInfo(proc).addUncaughtException(
								mProgDecl.getTypeFactory().lookupBoogieType(rt.getSootClass().getType()));
					} else {
						mProgDecl.getCache().getProcedureInfo(proc).addCaughtException(st, catchblock);
					}
				} else {
					Log.error("This should not happen");
					assert(false);
				}
			} else if (u instanceof Stmt) {
				if (u instanceof AssignStmt) {
					Value lhs = ((AssignStmt) u).getLeftOp();
					Value rhs = ((AssignStmt) u).getRightOp();
					if (lhs instanceof StaticFieldRef) {
						StaticFieldRef arg = (StaticFieldRef) ((AssignStmt) u).getLeftOp();
						Variable v = mProgDecl.getCache().lookupStaticField(arg.getField());
						proc.getModifiesGlobals().add(v);
					}
					if (lhs instanceof InstanceFieldRef) {
						switch (heapmode) {
						case Default:
							proc.getModifiesGlobals().add(mProgDecl.getProgram().getHeapVariable());
							break;
						case SimpleHeap:
							Variable v = mProgDecl.getCache().lookupStaticField(((InstanceFieldRef) lhs).getField());
							proc.getModifiesGlobals().add(v);
						}
					}
					if (lhs.getType().toString().contains("java.lang.String")) {
						// TODO maybe this should be moved to the string
						// handling as it is only a helper var
						switch (heapmode) {
						case Default:
							proc.getModifiesGlobals().add(mProgDecl.getProgram().getStringSize());
							break;
						case SimpleHeap:
						}

					}
					if (rhs instanceof NewArrayExpr) {
						// TODO maybe this should be moved to the array handling
						// as it is only a helper var
						BoogieType t = mProgDecl.getTypeFactory().lookupBoogieArrayType((ArrayType) rhs.getType());
						if (t == BoogieBaseTypes.getIntArrType()) {
							proc.getModifiesGlobals().add(mProgDecl.getProgram().getIntArraySize());
						} else if (t == BoogieBaseTypes.getRealArrType()) {
							proc.getModifiesGlobals().add(mProgDecl.getProgram().getRealArraySize());
						} else if (t instanceof RefArrayType) {
							proc.getModifiesGlobals().add(mProgDecl.getProgram().getRefArraySize());
						} else {
							// TODO this has to be changed once mulitarrays are
							// handled
							proc.getModifiesGlobals().add(mProgDecl.getProgram().getRefArraySize());
						}
					}
					if (rhs instanceof NewMultiArrayExpr) {
						// TODO maybe this should be moved to the array handling
						// as it is only a helper var
						// proc.modifiesGlobals.add(mProgDecl.getProgram().refArrSize);
					}

				}
				Stmt st = (Stmt) u;
				if (st.containsInvokeExpr()) {
					SootMethod called = st.getInvokeExpr().getMethod();
					if (!visited.contains(called)) {
						addUncaughtExceptionsAndModifiesClause(called, visited, heapmode);
					}
					// TODO check if this recursion works for large programs
					BoogieProcedure cproc = mProgDecl.getCache().lookupProcedure(called, heapmode);

					// build the call graph
					proc.getCalledProcedures().add(cproc);
					cproc.getCallingProcedures().add(proc);

					// Note that we cannot compute the the modifies clause
					// directly due to recursion.
					// hence, we add create a hashmap which we can use later on
					// to lookup the final modifies clause.
					mProgDecl.getCallDependencyMap().get(proc).addAll(mProgDecl.getCallDependencyMap().get(cproc));

					for (SootClass e : called.getExceptions()) {
						Trap catchblock = findCatchBlock(st, e, tug);
						if (catchblock == null) {
							m.addExceptionIfAbsent(e);
							mProgDecl.getCache().getProcedureInfo(proc)
									.addUncaughtException(mProgDecl.getTypeFactory().lookupBoogieType(e.getType()));
						} else {
							mProgDecl.getCache().getProcedureInfo(proc).addCaughtException(st, catchblock);
						}
					}
				}
			}
		}
	}

	private Trap returnNestedTrap(Trap a, Trap b, UnitGraph ug) {
		if (getTryBlock(ug, a.getBeginUnit(), a.getEndUnit(), new ArrayList<Unit>())
				.containsAll(getTryBlock(ug, b.getBeginUnit(), b.getEndUnit(), new ArrayList<Unit>()))) {
			return b;
		} else if (getTryBlock(ug, b.getBeginUnit(), b.getEndUnit(), new ArrayList<Unit>())
				.containsAll(getTryBlock(ug, a.getBeginUnit(), a.getEndUnit(), new ArrayList<Unit>()))) {
			return a;
		}
		// TODO we should throw an error here
		return null;
	}

	private HashSet<Stmt> getTryBlock(UnitGraph ug, Unit current, Unit endOfTry, ArrayList<Unit> visited) {
		HashSet<Stmt> ret = new HashSet<Stmt>();
		if (visited.contains(current))
			return ret;
		visited.add(current);
		for (Unit u : ug.getSuccsOf(current)) {
			if (u != endOfTry) {
				HashSet<Stmt> suffix = getTryBlock(ug, u, endOfTry, visited);
				if (suffix.size() > 0) {
					ret.addAll(suffix);
					ret.add((Stmt) current);
				}
			} else {
				ret.add((Stmt) current);
			}
		}
		return ret;
	}

	private Trap findCatchBlock(Stmt stmt, SootClass throwntype, UnitGraph ug) {
		Trap currentCatch = null;
		// Log.info("find trap for " + throwntype.toString());
		ug.getBody().validateTraps();
		for (Trap t : ug.getBody().getTraps()) {
			// check if the current trap can handle exceptions of type
			// throwntype or a superclass of it
			if (mProgDecl.getTypeFactory().compareTypes(throwntype.getType(), t.getException().getType()) >= 0) {
				// Log.error(throwntype.toString() + " cannot handle " +
				// t.getException().getType().toString());
				continue;
			}

			HashSet<Stmt> tryblock = getTryBlock(ug, t.getBeginUnit(), t.getEndUnit(), new ArrayList<Unit>());
			for (Unit u : tryblock) {
				if (stmt == (Stmt) u) {
					if (currentCatch != null) {
						currentCatch = returnNestedTrap(currentCatch, t, ug);
					} else {
						currentCatch = t;
					}
					break;
				}
			}
		}
		return currentCatch;
	}
}
