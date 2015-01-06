package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

// Inliner for procedures with overall unique variable identifiers.
public class ProcedureInliner implements IUnmanagedObserver {

	private IUltimateServiceProvider mServices;
	private Logger mLogger;
	private Unit mAstUnit;

	// Procedures have to be in exactly one map; keys are the identifiers of the procedures
	private HashMap<String, Procedure> mFlatProcedures = new HashMap<String, Procedure>();
	private HashMap<String, Procedure> mNonFlatProcedures = new HashMap<String, Procedure>();
	private ArrayList<Declaration> mNonProcedureDeclarations = new ArrayList<Declaration>();
	
	// Global list of all labels
	private HashSet<String> mAllLabels = new HashSet<String>();
	
	public ProcedureInliner(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	@Override
	public void init() throws Throwable {
	}

	@Override
	public void finish() throws Throwable {
		//mLogger.error(mAstUnit); // debug output
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		return null;
	}

	@Override
	public boolean performedChanges() {
		return true;
	}

	// TODO
	// for every non-flat procedure p
	// inline(p, {});
	// --------------------
	// inline(p, parents) :=
	//   if p in parents
	//     error: possible recursion!
	//   for every called procedure c in p
	//     if c is not flat
	//       inline(c, {p} u parents)
	//     inline c into p // this changes p
	//   mark p as flat
	@Override
	public boolean process(IElement root) throws Throwable {
		// Store the first node of the AST and use it to process the AST manually
		if (root instanceof Unit) {
			mAstUnit = (Unit) root;
			sortAndMakeLabelsUnique();
			HashSet<String> procIds = new HashSet<String>();
			procIds.addAll(mFlatProcedures.keySet());
			procIds.addAll(mNonFlatProcedures.keySet());			
			for (String procId : procIds) {
				Procedure proc = mNonFlatProcedures.get(procId);
				if (proc == null)
					continue;
				flatten(proc, new HashSet<Procedure>());
			}
			ArrayList<Declaration> newDecls = new ArrayList<Declaration>(mNonProcedureDeclarations);
			newDecls.addAll(mFlatProcedures.values());
			mAstUnit.setDeclarations(newDecls.toArray(new Declaration[newDecls.size()]));
			
			return false;
		}
		return true;
	}

	// distinct between flat and non-flat procedures
	// make all labels globally unique
	private void sortAndMakeLabelsUnique() {
		Declaration[] oldDecls = mAstUnit.getDeclarations();
		Declaration[] newDecls = new Declaration[oldDecls.length];
		for (int i = 0; i < oldDecls.length; ++i) {
			Declaration decl = oldDecls[i];
			if (!(decl instanceof Procedure)) {
				newDecls[i] = decl;
				mNonProcedureDeclarations.add(decl);
				continue;
			}
			Procedure proc = (Procedure) decl;
			Body body = proc.getBody();
			if (body == null) {
				mFlatProcedures.put(proc.getIdentifier(), proc);
				continue;
			}
			Statement[] oldBlock = proc.getBody().getBlock();
			Statement[] newBlock = new Statement[oldBlock.length];
			HashMap<String, String> labelMapping = new HashMap<String, String>(); // local name mapping for labels
			boolean isFlat = true;
			ArrayList<Integer> gotoStatementIndices = new ArrayList<Integer>();
			for (int j = 0; j < oldBlock.length; ++j) {
				Statement stat = oldBlock[j];
				if (stat instanceof CallStatement) {
					isFlat = false;
					newBlock[j] = stat;
				} else if (stat instanceof GotoStatement) {
					gotoStatementIndices.add(j);
					newBlock[j] = stat;
				} else if (stat instanceof Label) {
					Label l = (Label) stat;
					int uniqueNumber = 1;
					String newLabelName;
					do {
						newLabelName = proc.getIdentifier() + "_" + l.getName();
						if (uniqueNumber > 1)
							newLabelName += "#" + uniqueNumber;
						++uniqueNumber;
					} while (mAllLabels.contains(newLabelName));
					mAllLabels.add(newLabelName);
					labelMapping.put(l.getName(), newLabelName);
					newBlock[j] = new Label(l.getLocation(), newLabelName);
				} else {
					newBlock[j] = stat;
				}
			}
			// map goto statements to new label names
			for (int j : gotoStatementIndices) {
				GotoStatement g = (GotoStatement) oldBlock[j];
				String[] oldLabels = g.getLabels();
				String[] newLabels = new String[oldLabels.length];
				for (int k = 0; k < oldLabels.length; ++k) {
					newLabels[k] = labelMapping.get(oldLabels[k]);
				}
				newBlock[j] = new GotoStatement(g.getLocation(), newLabels);
			}
			(isFlat ? mFlatProcedures : mNonFlatProcedures).put(proc.getIdentifier(), proc);
			// change only block from body
			newDecls[i] = new Procedure(proc.getLocation(), proc.getAttributes(), proc.getIdentifier(),
					proc.getTypeParams(), proc.getInParams(), proc.getOutParams(), proc.getSpecification(),
					new Body(body.getLocation(), body.getLocalVars(), newBlock));
		}
		mAstUnit.setDeclarations(newDecls);
	}

	/**
	 * Recusivly inline all calls inside this procedure.
	 * @param proc Procedure which included calls should be inlined.
	 * @param parents Parent Procedure, its parent and so on.
	 * @return Flat Procedure.
	 */
	private Procedure flatten(Procedure proc, HashSet<Procedure> parents) {
		if (mFlatProcedures.values().contains(proc)) {
			return proc;
		} else if (parents.contains(proc)) {
			throw new UnsupportedOperationException("Can't inline possible recursion.");
		}
		Body body = proc.getBody(); // not null, because proc is not flat
		ArrayList<Statement> newBlock = new ArrayList<Statement>();
		HashSet<String> callees = new HashSet<String>(); // names of all functions called
		for (Statement s : body.getBlock()) {
			newBlock.addAll(flattenStatement(proc, parents, s, callees));
		}
		// Add local variables, also these from the called procedures (callees)
		ArrayList<VariableDeclaration> newLocalVars = new ArrayList<VariableDeclaration>();
		for (VariableDeclaration vd : body.getLocalVars()) {
			newLocalVars.add(vd);
		}
		for (String calleeId : callees) {
			Procedure callee = mFlatProcedures.get(calleeId);
			for (VarList[] vl : new VarList[][]{callee.getInParams(), callee.getOutParams()}) {
				if (vl.length > 0) {
					// TODO keep Attributes?
					// TODO which location is the closest?
					newLocalVars.add(new VariableDeclaration(callee.getLocation(), new Attribute[0], vl)); 
				}
			}
			Body calleeBody = callee.getBody();
			if (calleeBody != null) {
				for (VariableDeclaration vd : calleeBody.getLocalVars()) {
					newLocalVars.add(vd);
				}
			}
		}

		Procedure newProc = new Procedure(proc.getLocation(), proc.getAttributes(), proc.getIdentifier(),
				proc.getTypeParams(), proc.getInParams(), proc.getOutParams(), proc.getSpecification(),
				new Body(body.getLocation(), newLocalVars.toArray(new VariableDeclaration[newLocalVars.size()]),
						newBlock.toArray(new Statement[newBlock.size()])));
		mNonFlatProcedures.remove(proc.getIdentifier());
		mFlatProcedures.put(newProc.getIdentifier(), newProc);
		return newProc;
	}
	
	/**
	 * Flatten a statement.
	 * A statement is flat, if it doesn't contain a CallStatement (if and while can contain other Statements).
	 * @param proc Procedure containing the statement.
	 * @param parents Parent Procedure, its parent and so on.
	 * @param stat Statement to flat.
	 * @param callees All called procedures of the statement will be added (use for local variable declaration).
	 * @return Flat sequence of statements. Only one statement, iff nothing was called inside the statement.
	 */
	private ArrayList<Statement> flattenStatement(Procedure proc, HashSet<Procedure> parents,
			Statement stat, HashSet<String> callees) {

		ArrayList<Statement> flatStat = new ArrayList<Statement>();
		if (stat instanceof CallStatement) {
			CallStatement cs = (CallStatement) stat;
			if (cs.isForall()) {
				throw new UnsupportedOperationException("Cannot inline \"call forall\" yet.");
			}
			Procedure callee = mFlatProcedures.get(cs.getMethodName());
			if (callee == null) { 
				callee = mNonFlatProcedures.get(cs.getMethodName());
				assert callee != null;
				HashSet<Procedure> calleeParents = new HashSet<Procedure>(parents);
				calleeParents.add(proc);
				callee = flatten(callee, calleeParents);
			}
			callees.add(callee.getIdentifier());
			// Assign arguments to input parameters --------------
			ArrayList<VariableLHS> lhs = new ArrayList<VariableLHS>();
			for (VarList vl : callee.getInParams()) {
				for (String id : vl.getIdentifiers()) {
					// TODO is this declInfo really the right one?
					DeclarationInformation declInfo = new DeclarationInformation(
							DeclarationInformation.StorageClass.LOCAL, proc.getIdentifier());
					lhs.add(new VariableLHS(cs.getLocation(), vl.getType().getBoogieType(), id, declInfo));
				}
			}
			assert lhs.size() == cs.getArguments().length;
			if (lhs.size() > 0) {
				flatStat.add(new AssignmentStatement(cs.getLocation(), lhs.toArray(new VariableLHS[lhs.size()]),
						cs.getArguments()));					
			}
			// "call procedure" (inline specification and body) --------------
			flatStat.addAll(inlineVersion(callee, cs.getLocation(), proc));
			// assign output parameters --------------
			ArrayList<Expression> rhs = new ArrayList<Expression>();
			for (VarList vl : callee.getOutParams()) {
				for (String id : vl.getIdentifiers()) {
					// TODO is this declInfo really the right one?
					DeclarationInformation declInfo = new DeclarationInformation(
							DeclarationInformation.StorageClass.LOCAL, proc.getIdentifier());
					rhs.add(new IdentifierExpression(cs.getLocation(), vl.getType().getBoogieType(), id, declInfo));
				}
			}
			assert cs.getLhs().length == rhs.size();
			if (rhs.size() > 0) {
				flatStat.add(new AssignmentStatement(cs.getLocation(), cs.getLhs(),
						rhs.toArray(new Expression[rhs.size()])));					
			}
		} else if (stat instanceof WhileStatement) {
			WhileStatement whileStat = (WhileStatement) stat;
			ArrayList<Statement> whileBody = new ArrayList<Statement>();
			for (Statement s : whileStat.getBody()) {
				whileBody.addAll(flattenStatement(proc, parents, s, callees));
			}
			flatStat.add(new WhileStatement(whileStat.getLocation(), whileStat.getCondition(),
					whileStat.getInvariants(), whileBody.toArray(new Statement[whileBody.size()])));
		} else if (stat instanceof IfStatement) {
			IfStatement ifStat = (IfStatement) stat;
			ArrayList<Statement> thenPart = new ArrayList<Statement>();
			ArrayList<Statement> elsePart = new ArrayList<Statement>();
			for (Statement s : ifStat.getThenPart()) {
				thenPart.addAll(flattenStatement(proc, parents, s, callees));
			}
			for (Statement s : ifStat.getElsePart()) {
				elsePart.addAll(flattenStatement(proc, parents, s, callees));
			}
			flatStat.add(new IfStatement(ifStat.getLocation(), ifStat.getCondition(),
					thenPart.toArray(new Statement[thenPart.size()]),
					elsePart.toArray(new Statement[elsePart.size()])));
		} else { // Statement is already flat			
			flatStat.add(stat);
		}
		return flatStat;
	}
	
	// Create a sequence of Statements, which replaces a single (!: do not use multiple times!) call to this function.
	// assignments and variable declaration have to be added manually.
	// only for flat procedures (without calls).
	private ArrayList<Statement> inlineVersion(Procedure proc, ILocation callLocation, Procedure caller) {
		ArrayList<Statement> inlineBlock = new ArrayList<Statement>();
		ArrayList<VariableLHS> modifiesGlobalVars = new ArrayList<VariableLHS>();
		DeclInfoTransformer declInfoTransformer = new DeclInfoTransformer(caller.getIdentifier());

		String endLabel;
		int uniqueNumber = 1;
		do {
			endLabel = "endBody_" + proc.getIdentifier();
			if (uniqueNumber > 1)
				endLabel += "#" + uniqueNumber;
			++uniqueNumber;
		} while (mAllLabels.contains(endLabel));
		mAllLabels.add(endLabel);
		
		Specification[] specs = proc.getSpecification();
		ArrayList<Statement> inlinedEnsures = new ArrayList<Statement>();
		if (specs != null) {
			for (Specification spec : specs) {
				if (spec instanceof RequiresSpecification) {
					RequiresSpecification s = (RequiresSpecification) spec;
					Expression newExpr = declInfoTransformer.processExpression(s.getFormula());
					if (s.isFree()) {
						inlineBlock.add(new AssumeStatement(callLocation, newExpr));
					} else {
						inlineBlock.add(new AssertStatement(callLocation, newExpr));						
					}
				} else if (spec instanceof EnsuresSpecification) {
					EnsuresSpecification s = (EnsuresSpecification) spec;
					Expression newExpr = declInfoTransformer.processExpression(s.getFormula());
					// ensures is always inlined as an assume, because we don't want to check it for every call.
					// The called procedure remains in the program. The ensures specifications are checked there.
					inlinedEnsures.add(new AssumeStatement(callLocation, newExpr));
				} else if (spec instanceof ModifiesSpecification) {
					ModifiesSpecification s = (ModifiesSpecification) spec;
					for (VariableLHS id : s.getIdentifiers()) {
						modifiesGlobalVars.add(id); // TODO create new VariableLHS with better ILocation
					}
				}
				// modifies can be discarded
				// loopInvarant shouldn't occur here
			}		
		}		
		Body body = proc.getBody();
		if (body == null) {
			if (modifiesGlobalVars.size() > 0) {
				VariableLHS[] modifiedVars = new VariableLHS[modifiesGlobalVars.size()];
				modifiesGlobalVars.toArray(modifiedVars);
				inlineBlock.add(new HavocStatement(callLocation, modifiedVars));				
			}
		} else {
			ArrayList<VariableLHS> localVars = new ArrayList<VariableLHS>();
			for (VariableDeclaration vd : body.getLocalVars()) {
				for (VarList vl : vd.getVariables()) {
					for (String id : vl.getIdentifiers()) {
						// TODO is this declInfo really the right one?
						DeclarationInformation declInfo = new DeclarationInformation(
								DeclarationInformation.StorageClass.LOCAL, caller.getIdentifier());
						localVars.add(new VariableLHS(callLocation, vl.getType().getBoogieType(), id, declInfo));
					}
				}
			}
			if (localVars.size() > 0)
				inlineBlock.add(new HavocStatement(callLocation, localVars.toArray(new VariableLHS[localVars.size()])));
			
			HashMap<String, String> renamedLabels = new HashMap<String, String>(); // key = old name, value = new name
			ArrayList<Integer> gotoStatementIndices = new ArrayList<Integer>(); // indicies of all Gotos in List inlineBlock
			for (Statement s : body.getBlock()) {
				if (s instanceof ReturnStatement) {
					inlineBlock.add(new GotoStatement(s.getLocation(), new String[]{endLabel}));
				} else if (s instanceof Label) {
					Label lbl = (Label) s;
					if (mAllLabels.contains(lbl.getName())) {
						String newLabelName;
						int uniqueNum = 1;
						do {
							newLabelName = lbl.getName();
							if (uniqueNum > 1)
								newLabelName += "#" + uniqueNumber;
							++uniqueNum;
						} while (mAllLabels.contains(newLabelName));
						mAllLabels.add(newLabelName);
						renamedLabels.put(lbl.getName(), newLabelName);
						inlineBlock.add(new Label(lbl.getLocation(), newLabelName));						
					} else {
						inlineBlock.add(lbl);
					}
				} else {
					if (s instanceof GotoStatement)
						gotoStatementIndices.add(inlineBlock.size());
					inlineBlock.add(declInfoTransformer.processStatement(s));				
				}
			}
			// Update goto statements to renamed labels
			for (int i : gotoStatementIndices) {
				if (inlineBlock.get(i) instanceof GotoStatement) {
					GotoStatement g = (GotoStatement) inlineBlock.get(i);
					boolean changed = false;
					String[] oldLabels = g.getLabels();
					String[] newLabels = new String[oldLabels.length];
					for (int j = 0; j < oldLabels.length; ++j) {
						String newLabelName = renamedLabels.get(oldLabels[j]);						
						changed = newLabelName != null;
						if (changed) {
							newLabels[j] = newLabelName;
						} else {
							newLabels[j] = oldLabels[j];
						}
					}
					if (changed) {
						inlineBlock.set(i, new GotoStatement(g.getLocation(), newLabels));
					}
				}
				
			}
		}
		inlineBlock.add(new Label(callLocation, endLabel));
		inlineBlock.addAll(inlinedEnsures); // has to be after the endLabel, or it would be skipped, when using return.
		
		return inlineBlock;
	}

}





