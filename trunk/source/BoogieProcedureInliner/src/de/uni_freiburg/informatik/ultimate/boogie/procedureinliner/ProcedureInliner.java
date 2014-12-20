package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.preprocessor.Activator;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

// Inliner for procedures with overall unique variable identifiers.
// TODO implement
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
	
	// inline all calls inside this procedure
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
			if (s instanceof CallStatement) {
				CallStatement cs = (CallStatement) s;
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
						lhs.add(new VariableLHS(null, vl.getType().getBoogieType(), id, declInfo));
					}
				}
				assert lhs.size() == cs.getArguments().length;
				if (lhs.size() > 0) {
					newBlock.add(new AssignmentStatement(
							null, lhs.toArray(new VariableLHS[lhs.size()]), cs.getArguments()));					
				}
				// "call procedure" (inline specification and body) --------------
				newBlock.addAll(inlineVersion(callee));
				// assign output parameters --------------
				ArrayList<Expression> rhs = new ArrayList<Expression>();
				for (VarList vl : callee.getOutParams()) {
					for (String id : vl.getIdentifiers()) {
						// TODO is this declInfo really the right one?
						DeclarationInformation declInfo = new DeclarationInformation(
								DeclarationInformation.StorageClass.LOCAL, proc.getIdentifier());
						rhs.add(new IdentifierExpression(null, vl.getType().getBoogieType(), id, declInfo));
					}
				}
				assert cs.getLhs().length == rhs.size();
				if (rhs.size() > 0) {
					newBlock.add(new AssignmentStatement(null, cs.getLhs(), rhs.toArray(new Expression[rhs.size()])));					
				}
			} else {
				newBlock.add(s);
			}
		}
		// Add local variables from all callees
		ArrayList<VariableDeclaration> newLocalVars = new ArrayList<VariableDeclaration>();
		for (VariableDeclaration vd : body.getLocalVars()) {
			newLocalVars.add(vd);
		}
		for (String calleeId : callees) {
			Procedure callee = mFlatProcedures.get(calleeId);
			for (VarList[] vl : new VarList[][]{callee.getInParams(), callee.getOutParams()}) {
				if (vl.length > 0)
					newLocalVars.add(new VariableDeclaration(null, new Attribute[0], vl));
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
	
	// Create a sequence of Statements, which replaces a single (!: do not use multiple times!) call to this function.
	// assignments and variable declaration have to be added manually.
	// only for flat procedures (without calls).
	private ArrayList<Statement> inlineVersion(Procedure proc) {
		ArrayList<Statement> inlineBlock = new ArrayList<Statement>();
		
		String startLabel, endLabel;
		int uniqueNumber = 1;
		do {
			startLabel = "call_" + proc.getIdentifier();
			endLabel = "endCall_" + proc.getIdentifier();
			if (uniqueNumber > 1) {
				startLabel += "#" + uniqueNumber;
				endLabel += "#" + uniqueNumber;
			}
			++uniqueNumber;
		} while (mAllLabels.contains(startLabel) || mAllLabels.contains(endLabel));
		mAllLabels.add(startLabel);
		mAllLabels.add(endLabel);
		
		inlineBlock.add(new Label(null, startLabel));
		
		Specification[] specs = proc.getSpecification();
		ArrayList<AssumeStatement> assumes = new ArrayList<AssumeStatement>();
		if (specs != null) {
			for (Specification spec : specs) {
				if (spec instanceof RequiresSpecification) {
					RequiresSpecification s = (RequiresSpecification) spec;
					inlineBlock.add(new AssertStatement(null, s.getFormula()));
				} else if (spec instanceof EnsuresSpecification) {
					EnsuresSpecification s = (EnsuresSpecification) spec;
					assumes.add(new AssumeStatement(null, s.getFormula()));
				}
				// modifies can be discarded
				// loopInvarant shouldn't occur here
			}		
		}		
		Body body = proc.getBody();
		if (body != null) {
			ArrayList<VariableLHS> localVars = new ArrayList<VariableLHS>();
			for (VariableDeclaration vd : body.getLocalVars()) {
				for (VarList vl : vd.getVariables()) {
					for (String id : vl.getIdentifiers()) {
						localVars.add(new VariableLHS(null, id)); // TODO preserve IType and DeclarationInformation
					}
				}
			}
			if (localVars.size() > 0)
				inlineBlock.add(new HavocStatement(null, localVars.toArray(new VariableLHS[localVars.size()])));
			
			for (Statement s : body.getBlock()) {
				if (s instanceof ReturnStatement) {
					inlineBlock.add(new GotoStatement(s.getLocation(), new String[]{endLabel}));
				} else {
					inlineBlock.add(s);					
				}
			}
		}
		inlineBlock.addAll(assumes);
		inlineBlock.add(new Label(null, endLabel));
		
		return inlineBlock;
	}

}





