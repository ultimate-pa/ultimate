package de.uni_freiburg.informatik.ultimate.plugins.kojak;

import java.util.ArrayDeque;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.Predicate;

public class Split {

	private SmtManager mSmtManager;
	
	public Split(SmtManager smt_Manager) {
		mSmtManager = smt_Manager;
	}
	
	//splits all inner nodes on the path and extends their assertions with corresponding interpolants
	public HashSet<CodeBlock> split(Pair<KojakProgramPoint[], NestedWord<CodeBlock>> errorPath, Predicate[] interpolants){
		HashSet<CodeBlock>  slicableEdges = new HashSet<CodeBlock>();
		KojakProgramPoint[] pathPoints = errorPath.getEntry1();
		ArrayDeque<Predicate> interpolantStack = fixInterpolantArray(errorPath.getEntry2(), interpolants);
		for(KojakProgramPoint currentPP: pathPoints) {
			if(interpolantStack.isEmpty())
				break;
			Predicate interpolant = interpolantStack.removeLast();
			KojakProgramPoint splitPP =createSplitPP(currentPP, interpolant);
			if(splitPP == null) {
				continue;
			}
			slicableEdges.addAll(createSplitEdges(currentPP, splitPP, errorPath.getEntry2()));
		}
		return slicableEdges;
	}
	
	private HashSet<CodeBlock> createSplitEdges(KojakProgramPoint currentPP,KojakProgramPoint splitPP, NestedWord<CodeBlock> nestedWord) {
		HashSet<CodeBlock> slicableEdges = new HashSet<CodeBlock>();
		for(RCFGEdge edge: currentPP.getIncomingEdges()) {
			if(edge instanceof CodeBlock) {
				CodeBlock cd = (CodeBlock)edge;
				KojakProgramPoint sourcePP = (KojakProgramPoint)cd.getSource();
				CodeBlock splitCB = cd.getCopy(sourcePP, splitPP);
				slicableEdges.add(cd);
				slicableEdges.add(splitCB);
			}
		}
		
		for(RCFGEdge edge: currentPP.getOutgoingEdges()) {
			CodeBlock cd = (CodeBlock)edge;
			KojakProgramPoint targetPP = (KojakProgramPoint)cd.getTarget();
			CodeBlock splitCB = cd.getCopy(splitPP, targetPP);
			slicableEdges.add(cd);
			slicableEdges.add(splitCB);
			if(cd instanceof Call) {
				Call call = (Call)cd;
				int callPosition = getCallPositionOnNestedWord(call, nestedWord);
				if (callPosition >= 0) {
					try {
						int returnPosition = nestedWord.getReturnPosition(callPosition);
						Return returnStatement = (Return)nestedWord.getSymbolAt(returnPosition);
						Return newReturn = new Return(
								(KojakProgramPoint)returnStatement.getSource(),
								(KojakProgramPoint)returnStatement.getTarget(),
								(Call)splitCB,
								splitPP);
						slicableEdges.add(newReturn);
					} catch (IllegalArgumentException e){
						
					}
				}
			}
		}
		return slicableEdges;
	}
	
	private int getCallPositionOnNestedWord(Call call, NestedWord<CodeBlock> nestedWord) {
		for(int i = 0; i<nestedWord.length();i++) {
			if (nestedWord.getSymbolAt(i).equals(call)){
				return i;
			}
		}
		return -1;
	}
	
	private KojakProgramPoint createSplitPP(KojakProgramPoint currentPP, Predicate interpolant) {
		if (interpolant.equals(KojakEngine.getTruePredicate())) {
			return null;
		} else if (interpolant.equals(KojakEngine.getFalsePredicate())) {
			return null;
		} else {
			KojakProgramPoint splitPP = newPPFrom(currentPP);
			Predicate predicate = currentPP.getPredicate();
			
			Predicate newPosPredicate =	mSmtManager.and(
					predicate, interpolant);
			currentPP.setPredicateInKojakAnnotation(newPosPredicate);
			
			Predicate newNegPredicate = mSmtManager.and(
					predicate, mSmtManager.not(interpolant));
			splitPP.initKojakAnnotation(newNegPredicate);
			return splitPP;
		}
	}
	
	private ArrayDeque<Predicate> fixInterpolantArray(NestedWord<CodeBlock> nestedWord, Predicate[] interpolants) {
		ArrayDeque<Predicate> interpolantStack =
				new ArrayDeque<Predicate>();

		for (int i = 0; i < nestedWord.length()-1; i++) {
			CodeBlock codeBlock = nestedWord.getSymbolAt(i);
			if(codeBlock instanceof Call) {
				try{
					nestedWord.getReturnPosition(i);
					interpolantStack.push(KojakEngine.getTruePredicate());
				} catch(IllegalArgumentException e) {
					interpolantStack.push(interpolants[i]);
				}
			} else {
				interpolantStack.push(interpolants[i]);
			}
		}
		return interpolantStack;
	}
	
	private KojakProgramPoint newPPFrom(KojakProgramPoint oldPP) {
		return new KojakProgramPoint(
				oldPP.getPosition(),
				oldPP.getProcedure(),
				oldPP.isErrorLocation(),
				oldPP.getAstNode());
	}
}
