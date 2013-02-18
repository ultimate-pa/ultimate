package local.stalin.automata.nwalibrary;

import java.util.Collection;

public class ContentFactory<Content> {
	
	public Content createContentOnIntersection(Content c1, Content c2) {
		return null;
	}
	
	public Content createContentOnDeterminization(
			Collection<Pair<Content, Content>> cPairList) {
		return null;
	}
	
	public Content createSinkStateContent() {
		return null;
	}
	
	public Content createEmptyStackContent() {
		return null;
	}

	public Content createContentOnDifference(Content c1,
			Collection<Pair<Content, Content>> cPairList) {
		return null;
	}
	
	public Content getContentOnPetriNet2FiniteAutomaton(
			Collection<Content> cList) {
		return null;
	}
	
	public Content getContentOnConcurrentProduct(Content c1, Content c2) {
		return createContentOnIntersection(c1, c2);
	}

	public Content getWhiteContent(Content c) {
		return c;
	}
	
	public Content getBlackContent(Content c) {
		return c;
	}
}
