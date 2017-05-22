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
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

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
		// TODO filter bottoms
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
	
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addEquality(NODE node1, NODE node2,
			EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> inputConstraint) {
//		if (factory.isDebugMode()) {
//			factory.getLogger().debug("VPFactoryHelpers: addEquality(" + node1 + ", " + node2 + ", " + "..." + ") -- "
//					+ originalStates.size() + " input states");
//		}

		if (node1 == node2 || node1.equals(node2)) {
			return inputConstraint;
		}
		
		final Set<EqConstraint<ACTION, NODE, FUNCTION>> newConstraints = new HashSet<>();

		for (EqConstraint<ACTION, NODE, FUNCTION> originalState : inputConstraint.getConstraints()) {
			newConstraints.addAll(addEquality(node1, node2, originalState).getConstraints());
		}
		
		return getDisjunctiveConstraint(newConstraints);
	}
	

	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> addEquality(NODE node1, NODE node2,
			EqConstraint<ACTION, NODE, FUNCTION> originalState) {
		
//		factory.getBenchmark().unpause(VPSFO.addEqualityClock);
//		if (factory.isDebugMode()) {
//			factory.getLogger().debug("VPFactoryHelpers: addEquality(" + node1 + ", " + node2 + ", " + "..." + ")");
//		}
		if (originalState.isBottom()) {
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return getDisjunctiveConstraint(Collections.singleton(originalState));
		}

		if (node1 == node2 || node1.equals(node2)) {
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
//			return Collections.singleton(originalState);
			return getDisjunctiveConstraint(Collections.singleton(originalState));
		}

//		final IVPStateOrTfStateBuilder<T, NODEID, ARRAYID> builder = factory.copy(originalState);
		
//		final EqGraphNode<NODE, FUNCTION> gn1 = builder.getEqGraphNode(node1);
//		final EqGraphNode<NODE, FUNCTION> gn2 = builder.getEqGraphNode(node2);
//		if (gn1.find() == gn2.find()) {
		if (originalState.areEqual(node1, node2)) {
			// the given identifiers are already equal in the originalState
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
//			return Collections.singleton(originalState);
			return getDisjunctiveConstraint(Collections.singleton(originalState));
		}

		EqConstraint<ACTION, NODE, FUNCTION> newConstraint = unfreeze(originalState);
		
//		builder.merge(gn1, gn2);
		newConstraint.merge(node1, node2);
//		builder.setIsTop(false);
//		final boolean contradiction = builder.checkContradiction();
		final boolean contradiction = newConstraint.checkForContradiction();
//		assert contradiction || VPDomainHelpers.disEqualityRelationIrreflexive(builder.getDisEqualitySet(), builder);
		if (contradiction) {
			final Set<EqConstraint<ACTION, NODE, FUNCTION>> result = Collections.singleton(getBottomConstraint());
			assert result.stream().filter(element -> element == null).count() == 0;
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
//			return result;
			return getDisjunctiveConstraint(result);
		}

		final EqConstraint<ACTION, NODE, FUNCTION> resultState = newConstraint;

		/**
		 * Propagate disequalites
		 */
		final Set<T> resultStates = new HashSet<>();
		for (final NODE other : originalState.getDisequalities(gn1.mNodeIdentifier)) {
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			resultStates.addAll(propagateDisEqualites(resultState, gn1, resultState.getEqGraphNode(other), factory));
//			factory.getBenchmark().unpause(VPSFO.addEqualityClock);
		}
		for (final NODE other : originalState.getDisequalities(gn2.mNodeIdentifier)) {
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			resultStates.addAll(propagateDisEqualites(resultState, gn2, resultState.getEqGraphNode(other), factory));
//			factory.getBenchmark().unpause(VPSFO.addEqualityClock);
		}
		
		if (resultStates.isEmpty()) {
			assert resultState != null;
//			factory.getBenchmark().stop(VPSFO.addEqualityClock);
			return Collections.singleton(resultState);
		}
		
		// assert VPDomainHelpers.allStatesHaveSameVariables(resultStates);
		assert resultStates.stream().filter(element -> element == null).count() == 0;
//		factory.getBenchmark().stop(VPSFO.addEqualityClock);
		return resultStates;
		// TODO Auto-generated method stub
		return null;
	}

	public EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> addDisequality(
			EqDisjunctiveConstraint<ACTION, EqNode, EqFunction> disjunctiveConstraint) {
		// TODO Auto-generated method stub
		return null;
	}
	
	/**
	 * Takes a preState and two representatives of different equivalence classes. Under the assumption that a
	 * disequality between the equivalence classes has been introduced, propagates all the disequalities that follow
	 * from that disequality.
	 *
	 * @param originalStateCopy
	 * @param representative1
	 * @param representative2
	 * @return
	 */
	public EqDisjunctiveConstraint<ACTION, NODE, FUNCTION> propagateDisEqualites(
			final EqConstraint<ACTION, NODE, FUNCTION> originalStateCopy, 
			final NODE representative1,
			final NODE representative2) {

//		factory.getBenchmark().unpause(VPSFO.propagateDisEqualitiesClock);
//		if (factory.isDebugMode()) {
//			factory.getLogger().debug("VPFactoryHelpers: propagateDisEqualities(..)");
//		}

		Set<EqConstraint<ACTION, NODE, FUNCTION>> result = new HashSet<>();
		result.add(originalStateCopy);
		

		final HashRelation<FUNCTION, List<EqGraphNode<NODE, FUNCTION>>> ccchild1 = 
				originalStateCopy.getCCChild(representative1);
		final HashRelation<FUNCTION, List<EqGraphNode<NODE, FUNCTION>>> ccchild2 = 
				originalStateCopy.getCCChild(representative2);

		for (final FUNCTION arrayId : ccchild1.getDomain()) {
			for (final List<EqGraphNode<NODE, FUNCTION>> list1 : ccchild1.getImage(arrayId)) {
				for (final List<EqGraphNode<NODE, FUNCTION>> list2 : ccchild2.getImage(arrayId)) {
					final Set<STATE> intermediateResult = new HashSet<>(result);
					result = new HashSet<>();
					for (int i = 0; i < list1.size(); i++) {
						final EqGraphNode<NODE, FUNCTION> c1 = list1.get(i);
						final EqGraphNode<NODE, FUNCTION> c2 = list2.get(i);
						if (originalStateCopy.containsDisEquality(c1.find().mNodeIdentifier, c2.find().mNodeIdentifier)) {
							continue;
						}
						factory.getBenchmark().stop(VPSFO.propagateDisEqualitiesClock);
						result.addAll(
								addDisEquality(c1.mNodeIdentifier, c2.mNodeIdentifier, intermediateResult, factory));
						factory.getBenchmark().unpause(VPSFO.propagateDisEqualitiesClock);
					}
				}
			}
		}

		if (result.isEmpty()) {
			// no propagations -- return the input state
			factory.getBenchmark().stop(VPSFO.propagateDisEqualitiesClock);
			return Collections.singleton(originalStateCopy);
		}
		factory.getBenchmark().stop(VPSFO.propagateDisEqualitiesClock);
		return result;
	}

}
