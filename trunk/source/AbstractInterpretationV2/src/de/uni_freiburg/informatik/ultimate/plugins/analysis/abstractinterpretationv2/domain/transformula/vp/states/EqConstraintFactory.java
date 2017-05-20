package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPSFO;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqGraphNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;

public class EqConstraintFactory<
			ACTION extends IIcfgTransition<IcfgLocation>, 
			NODE extends IEqNodeIdentifier<NODE, FUNCTION>, 
			FUNCTION extends IEqFunctionIdentifier<FUNCTION>> {

	public EqConstraint<ACTION, NODE, FUNCTION> getEmptyConstraint() {
		return null;
	}

	public EqConstraint<ACTION, NODE, FUNCTION> getBottomConstraint() {
		return null;
	}

	public EqConstraint<ACTION, NODE, FUNCTION> unfreeze(EqConstraint<ACTION, NODE, FUNCTION> constraint) {
		assert constraint.isFrozen();
		// TODO Auto-generated method stub
		return null;
	}

	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> unfreeze(
			EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> constraint) {
		// TODO Auto-generated method stub
		return null;
	}

	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> 
			getDisjunctiveConstraint(Collection<EqConstraint<ACTION, NODE, FUNCTION>> constraintList) {
		return new EqDisjunctiveConstraint<ACTION, NODE, FUNCTION>(constraintList);
	}
	
	
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> conjoin(
			List<EqConstraint<ACTION, NODE, FUNCTION>> conjuncts) {
		final EqConstraint<ACTION, NODE, FUNCTION> newConstraint = getEmptyConstraint();
		
		for (EqConstraint<ACTION, NODE, FUNCTION> conjunct : conjuncts) {
			newConstraint.addNodes(conjunct.getAllNodes());
			
			for (Entry<NODE, NODE> eq : conjunct.getSupportingElementEqualities().entrySet()) {
				newConstraint.merge(eq.getKey(), eq.getValue());
			}
			
			for (VPDomainSymmetricPair<NODE> deq : conjunct.getElementDisequalities()) {
				newConstraint.addRawDisequality(deq.getFirst(), deq.getSecond());
			}
			
			for (Entry<FUNCTION, FUNCTION> aEq : conjunct.getSupportingFunctionEqualities()) {
				newConstraint.addFunctionEquality(aEq.getKey(), aEq.getValue());
			}
			
			for (VPDomainSymmetricPair<FUNCTION> aDeq : conjunct.getFunctionDisequalites()) {
				newConstraint.addFunctionDisequality(aDeq.getFirst(), aDeq.getSecond());
			}

			if (newConstraint.checkForContradiction()) {
				return getBottomConstraint();
			}
		}
		
		newConstraint.freeze();
		return newConstraint;
	}

	public EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> conjoinDisjunctiveConstraints(
			List<EqDisjunctiveConstraint<ACTION, EqNode, EqFunction>> conjuncts) {
		final List<Set<EqConstraint<ACTION, EqNode, EqFunction>>> listOfConstraintSets = conjuncts.stream()
				.map(conjunct -> conjunct.getConstraints()).collect(Collectors.toList());

		final Set<List<EqConstraint<ACTION, EqNode, EqFunction>>> crossProduct = 
				VPDomainHelpers.computeCrossProduct(listOfConstraintSets);

		final Set<EqConstraint<ACTION, EqNode, EqFunction>> constraintSet = crossProduct.stream()
				.map(constraintList -> mEqConstraintFactory.conjoin(constraintList))
				.collect(Collectors.toSet());

		return mEqConstraintFactory.getDisjunctiveConstraint(constraintSet);
	}

	public EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> addEquality(
			EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> disjunctiveConstraint) {
		
		factory.getBenchmark().unpause(VPSFO.addEqualityClock);
		if (factory.isDebugMode()) {
			factory.getLogger().debug("VPFactoryHelpers: addEquality(" + node1 + ", " + node2 + ", " + "..." + ")");
		}
		if (originalState.isBottom()) {
			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return Collections.singleton(originalState);
		}

		if (node1 == node2 || node1.equals(node2)) {
			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return Collections.singleton(originalState);
		}

		final IVPStateOrTfStateBuilder<T, NODEID, ARRAYID> builder = factory.copy(originalState);
		
		final EqGraphNode<NODEID, ARRAYID> gn1 = builder.getEqGraphNode(node1);
		final EqGraphNode<NODEID, ARRAYID> gn2 = builder.getEqGraphNode(node2);
		if (gn1.find() == gn2.find()) {
			// the given identifiers are already equal in the originalState
			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return Collections.singleton(originalState);
		}
		
		builder.merge(gn1, gn2);
		builder.setIsTop(false);
		final boolean contradiction = builder.checkContradiction();
		assert contradiction || VPDomainHelpers.disEqualityRelationIrreflexive(builder.getDisEqualitySet(), builder);
		if (contradiction) {
			final Set<T> result = Collections.singleton(factory.getBottomState(originalState));
			assert result.stream().filter(element -> element == null).count() == 0;
			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return result;
		}

		final T resultState = builder.build();

		/**
		 * Propagate disequalites
		 */
		final Set<T> resultStates = new HashSet<>();
		for (final NODEID other : originalState.getDisequalities(gn1.mNodeIdentifier)) {
			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			resultStates.addAll(propagateDisEqualites(resultState, gn1, resultState.getEqGraphNode(other), factory));
			factory.getBenchmark().unpause(VPSFO.addEqualityClock);
		}
		for (final NODEID other : originalState.getDisequalities(gn2.mNodeIdentifier)) {
			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			resultStates.addAll(propagateDisEqualites(resultState, gn2, resultState.getEqGraphNode(other), factory));
			factory.getBenchmark().unpause(VPSFO.addEqualityClock);
		}
		
		if (resultStates.isEmpty()) {
			assert resultState != null;
			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return Collections.singleton(resultState);
		}
		
		// assert VPDomainHelpers.allStatesHaveSameVariables(resultStates);
		assert resultStates.stream().filter(element -> element == null).count() == 0;
		factory.getBenchmark().stop(VPSFO.addEqualityClock);
		return resultStates;
		// TODO Auto-generated method stub
		return null;
	}

	public EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> addDisequality(
			EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> disjunctiveConstraint) {
		// TODO Auto-generated method stub
		return null;
	}
}
