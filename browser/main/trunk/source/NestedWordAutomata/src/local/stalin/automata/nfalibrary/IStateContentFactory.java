package local.stalin.automata.nfalibrary;

import java.util.List;

public interface IStateContentFactory<Content extends StateContent> {
	Content createContentOnIntersection(Content c1, Content c2);
	Content createContentOnDeterminization(List<Content> cList);
	Content createContentOnMinimization(List<Content> cList);
	Content createSinkStateContent();
}
