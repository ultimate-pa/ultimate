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

package org.joogie.soot;

import java.util.Iterator;
import java.util.Map;

import org.joogie.HeapMode;
import org.joogie.boogie.BoogieProcedure;
import org.joogie.util.Log;

import soot.Body;
import soot.BodyTransformer;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.Stmt;
import soot.util.Chain;

/**
 * Boogie Body Transformer
 * 
 * @author schaef
 */
public class BoogieBodyTransformer extends BodyTransformer {

	private final String mScope;
	private final HeapMode mHeapmode;

	public BoogieBodyTransformer(final String scope, HeapMode heapmode) {
		mScope = scope;
		mHeapmode = heapmode;
	}

	@Override
	@SuppressWarnings("rawtypes")
	protected void internalTransform(Body arg0, String arg1, Map arg2) {
		if (mScope != null) {
			SootMethod method = arg0.getMethod();
			SootClass clazz = method.getDeclaringClass();
			String packageName = clazz.getPackageName();

			if (!packageName.startsWith(mScope)) {
				return; // ignore current body
			}
		}

		// add method to report
		SootMethod sootMethod = arg0.getMethod();
		Log.debug("METHOD: " + sootMethod);
		transformStmtList(arg0);
	}

	/**
	 * Transforms a list of statements
	 * 
	 * @param body
	 *            Body
	 */
	private void transformStmtList(Body body) {
		boolean firstblock = true;

		BoogieProcedure proc = GlobalsCache.v().lookupProcedure(body.getMethod(), mHeapmode);
		BoogieHelpers.currentProcedure = proc;
		BoogieStmtSwitch bss = new BoogieStmtSwitch(proc, mHeapmode);

		Chain<Unit> units = body.getUnits();
		Iterator<Unit> stmtIt = units.snapshotIterator();

		while (stmtIt.hasNext()) {
			Stmt s = (Stmt) stmtIt.next();

			bss.prepareCurrentBlock(s); // initialize a BasicBlock, if the
										// current one is null
			if (firstblock) {
				firstblock = false;
				proc.setBodyRoot(bss.getCurrentBlock());
			}
			s.apply(bss);
		}

	}
}
/**
 * Identify finally blocks that are duplicated by the java complier. Remove the
 * duplicates and add a helper variable to indicate where the finally block
 * jumps back to.
 * 
 * @param m
 *            The current soot method
 */
// private void eliminateDuplicates(SootMethod m) {
// Chain<Unit> units = m.getActiveBody().getUnits();
// Iterator<Unit> stmtIt = units.snapshotIterator();
//
// HashMap<String,LinkedList<Stmt>> duplicatesMap = new
// HashMap<String,LinkedList<Stmt>>();
// LinkedList<String> duplicatedSequence = new LinkedList<String>();
// LinkedList<LinkedList<String>> duplicatedBlocks = new
// LinkedList<LinkedList<String>>();
//
// boolean lastWasDuplicated=false;
// Log.error("======"+m.getName());
// while (stmtIt.hasNext()) {
// Stmt s = (Stmt) stmtIt.next();
// String uniqueStmtId = getComparableStmtSigniture(s);
//
// Log.error(uniqueStmtId);
//
// if (!lastWasDuplicated) {
// duplicatedSequence = new LinkedList<String>();
// }
//
// if (!duplicatesMap.containsKey(uniqueStmtId)) {
// if (lastWasDuplicated && duplicatedSequence.size()>0) {
// //we found a sequence of duplicated statements
// addDuplicatedList(duplicatedSequence, duplicatedBlocks);
// }
// lastWasDuplicated=false;
// //add the current statement to the duplicates map so
// //that a duplicate is reported if the same stmt is
// //found again
// LinkedList<Stmt> stmts = new LinkedList<Stmt>();
// stmts.add(s);
// duplicatesMap.put(uniqueStmtId, stmts);
// } else {
// duplicatedSequence.add(uniqueStmtId);
//
// Log.error("duplicate found: "+ s.toString());
// Log.error(uniqueStmtId);
// Log.error("Duplicates are: ");
// for (Stmt d : duplicatesMap.get(uniqueStmtId)) {
// Log.error(d);
// }
// duplicatesMap.get(uniqueStmtId).add(s);
// lastWasDuplicated=true;
// }
//
// //TODO: is it possible that we have overlapping duplicated blocks?
//
// }
// /*
// * now we have the unique identifier of all blocks
// * of consecutive duplicated statements in duplicatedBlocks
// * and duplicatesMap gives us for each of these identifiers
// * all source statements that are associated with it.
// * Now, we select one duplicate, we have to introduce a
// * fresh variable, and add an assignment
// * to each predecessor of a duplicated block
// * that assigns this variable to a unique value. Then, at the
// * end of the duplicated block, we have to do a switch over
// * this variable to identify the jump target, depending on
// * where we came from. finally, we can delete all other
// * duplicates.
// */
// /*
// * TODO: comparing statements does not make sense, as the compiler
// * introduces fresh variables. The only way I can think of right now
// * is to check for duplicated line numbers and then test if they are
// * not immediate successors
// */
// if (duplicatedBlocks.size()>0) {
//
// for (LinkedList<String> seq : duplicatedBlocks) {
// LinkedList<Stmt> heads = duplicatesMap.get(seq.getFirst());
// LinkedList<Stmt> tails = duplicatesMap.get(seq.getLast());
// Unit first = heads.getFirst();
// Unit last = tails.getLast();
//
// LinkedList<UnitBox> finallyEntryPoints = new LinkedList<UnitBox>();
// for (Stmt head : heads) {
// finallyEntryPoints.addAll(head.getBoxesPointingToThis());
// }
//
// for (UnitBox ub : finallyEntryPoints) {
// Log.error("Unit Box " + ub.toString());
// }
// }
// }
// }
//
// private String getComparableStmtSigniture(Stmt s) {
// StringBuilder sb = new StringBuilder();
// for (Tag t : s.getTags()) {
// sb.append(t.toString()+ ":");
// }
// sb.append(s.getBoxesPointingToThis().toString());
// AbstractUnitPrinter aup =
// new AbstractUnitPrinter() {
// @Override
// public void fieldRef(SootFieldRef arg0) {
// output.append("?"+arg0.toString());
// }
//
// @Override
// public void identityRef(IdentityRef arg0) {
// output.append(arg0.toString());
// }
//
// @Override
// public void literal(String arg0) {
// output.append(arg0);
// }
//
// @Override
// public void methodRef(SootMethodRef arg0) {
// output.append(arg0);
// }
//
// @Override
// public void type(Type arg0) {
// output.append(arg0);
// }
//
// @Override
// public void unitRef(Unit arg0, boolean arg1) {
// arg0.toString(this);
// }
// @Override
// public void local(Local arg0) {
// output.append(arg0.getName()+"#"+arg0.getNumber());
// }
//
// };
// s.toString(aup);
// sb.append(aup.output().toString());
// return sb.toString();
// }
//
//
// private void addDuplicatedList(LinkedList<String> seq,
// LinkedList<LinkedList<String>> seqs) {
// for (LinkedList<String> seq_ : seqs) {
// if (seq_.size()==seq.size()) {
// boolean equal=true;
// for (int i=0;i<seq_.size();i++) {
// if (!seq_.get(i).contentEquals(seq.get(i))) {
// equal=false;
// break;
// }
// }
// //there is already a sequence like this.
// if (equal) return;
// }
// }
// seqs.add(seq);
// }
//
// }
