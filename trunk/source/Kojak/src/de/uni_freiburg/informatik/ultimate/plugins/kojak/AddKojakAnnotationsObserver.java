package de.uni_freiburg.informatik.ultimate.plugins.kojak;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.model.IEdge;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

public class AddKojakAnnotationsObserver implements IUnmanagedObserver{

	@Override
	public void init() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub
		
	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean process(IElement root) {
		HashSet<Return> returnSet = new HashSet<Return>();
		for(RCFGEdge rootEdge: ((RootNode)root).getOutgoingEdges()) {
			substituteProgramPoint(rootEdge, returnSet);
		}
		for (Return returnEdge: returnSet) {
			Call call = returnEdge.getCorrespondingCall();
			Return newReturn = new Return(
					(ProgramPoint)returnEdge.getSource(),
					(ProgramPoint)returnEdge.getTarget(),
					call);
			newReturn.setTransitionFormula(returnEdge.getTransitionFormula());
			returnEdge.disconnectSource();
			returnEdge.disconnectTarget();
		}
		return false;
	}

	private void substituteProgramPoint(
			RCFGEdge rootEdge,
			HashSet<Return> returnSet) {
		
		ProgramPoint pp = (ProgramPoint)rootEdge.getTarget();
		KojakProgramPoint kpp = new KojakProgramPoint(
				pp.getPosition(),
				pp.getProcedure(),
				pp.isErrorLocation(),
				pp.getAstNode());
		kpp.getPayload().getAnnotations().put("kojak", new KojakAnnotations());
		redirectIncomingEdges(pp, kpp);
		redirectOutgoingEdges(pp, kpp);
		for(RCFGEdge nextEdge: kpp.getOutgoingEdges()) {
			if (nextEdge instanceof Call) {
				continue;
			} else if (nextEdge instanceof Return) {
				returnSet.add((Return)nextEdge);
				continue;
			} else if(nextEdge.getTarget() instanceof KojakProgramPoint) {
				continue;
			} else {
				substituteProgramPoint(nextEdge, returnSet);
			}
		}
	}
	
	private void redirectIncomingEdges(ProgramPoint pp, KojakProgramPoint kpp) {
		RCFGEdge[] incomingEdges = new RCFGEdge[pp.getIncomingEdges().size()];
		pp.getIncomingEdges().toArray(incomingEdges);
		for(RCFGEdge edge: incomingEdges) {
			if (edge instanceof CodeBlock) {
				CodeBlock cd = (CodeBlock)edge;
				cd.disconnectTarget();
				cd.connectTarget(kpp);
			} else if (edge instanceof RootEdge){
				RootEdge rootEdge = (RootEdge)edge;
				rootEdge.setTarget(kpp);
				kpp.addIncoming(rootEdge);
				pp.removeIncoming(rootEdge);
			}
		}
	}
	
	private void redirectOutgoingEdges(ProgramPoint pp, KojakProgramPoint kpp) {
		IEdge[] outgoingEdges = new IEdge[pp.getOutgoingEdges().size()];
		pp.getOutgoingEdges().toArray(outgoingEdges);
		for(IEdge edge: outgoingEdges) {
			CodeBlock cd = (CodeBlock)edge;
			cd.disconnectSource();
			cd.connectSource(kpp);
		}
	}
}
