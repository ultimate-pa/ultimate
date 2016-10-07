package de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.Deque;
import java.util.List;
import java.util.Objects;
import java.util.function.Consumer;

import org.eclipse.cdt.core.dom.ast.IASTComment;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorElifStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorElseStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorEndifStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfdefStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIfndefStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorIncludeStatement;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorMacroExpansion;
import org.eclipse.cdt.core.dom.ast.IASTPreprocessorStatement;
import org.eclipse.cdt.core.dom.ast.IASTTranslationUnit;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.exceptions.UnbalancedConditionalDirectiveException;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.cdt.LocationResolver;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.implementation.DefaultNodeFactory;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTComment;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTConditionalBlock;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTIncludeDirective;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTMacroExpansion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTNodeFactory;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTOverlappingRegion;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTRegularNode;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.pst.interfaces.IPSTTranslationUnit;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.parser.util.ASTNodeUtils;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.HierarchicalSourceRangeComparator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceDocument;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.text.ISourceRange;

/**
 * Builder to create the PST from a given AST and source code.
 */
public class PSTBuilder {
	private final IASTTranslationUnit translationUnit;
	private final ISourceDocument sourceDocument;
	
	private IPSTNodeFactory nodeFactory;
	private LocationResolver locationResolver;
	
	private boolean createComments = true;
	private boolean createMacroExpansions = true;
	private boolean expandConditionalBlocks = true;

	private ConditionalBlock conditionalBlockRoot;
	private List<IPSTMacroExpansion> macroExpansions;
	private List<IPSTComment> comments;

	/**
	 * Create new builder instance.
	 * 
	 * @param ast AST instance
	 * @param sourceDocument source document 
	 */
	public PSTBuilder(IASTTranslationUnit ast, ISourceDocument sourceDocument) {
		translationUnit = Objects.requireNonNull(ast);
		this.sourceDocument = Objects.requireNonNull(sourceDocument);
	}

	public PSTBuilder setNodeFactory(IPSTNodeFactory nodeFactory) {
		this.nodeFactory = nodeFactory;
		return this;
	}
	
	public PSTBuilder setCreateComments(boolean createComments) {
		this.createComments = createComments;
		return this;
	}
	
	public PSTBuilder setCreateMacroExpansions(boolean createMacroExpansions) {
		this.createMacroExpansions = createMacroExpansions;
		return this;
	}
	
	public PSTBuilder setExpandConditionalBlocks(boolean expandConditionalBlocks) {
		this.expandConditionalBlocks = expandConditionalBlocks;
		return this;
	}
	
	
	/**
	 * @return new IPSTTranslationUnit instance
	 * @throws UnbalancedConditionalDirectiveException on unbalanced #if/#else/#endif directives
	 */
	public IPSTTranslationUnit build() {
		if (locationResolver == null) {
			locationResolver = new LocationResolver(translationUnit.getContainingFilename(), sourceDocument);
		}

		if (nodeFactory == null) {
			nodeFactory = new DefaultNodeFactory();
		}
		
		nodeFactory.setSourceDocument(sourceDocument);
		
		createPreprocessorNodes();
		IPSTTranslationUnit tu = createTree();
		insertRemainingPreprocessorNodes(tu);
		return tu;
	}

	
	private void createPreprocessorNodes() {
		conditionalBlockRoot = createConditionalBlockTree();
		
		macroExpansions = new ArrayList<>();
		if (createMacroExpansions) {
			for (IASTPreprocessorMacroExpansion expansion : translationUnit.getMacroExpansions()) {
				ISourceRange location = locationResolver.getSourceRangeInTranslationUnitFile(expansion);
				if (location != null) {
					macroExpansions.add(nodeFactory.createMacroExpansion(location, expansion));
				}
			}
		}
		
		comments = new ArrayList<>();
		if (createComments) {
			for (IASTComment comment : translationUnit.getComments()) {
				ISourceRange location = locationResolver.getSourceRangeInTranslationUnitFile(comment);
				if (location != null) {
					comments.add(nodeFactory.createComment(location, comment));
				}
			}
		}
	}
	
	
	private static class ConditionalBlock implements ISourceRange {
		final ConditionalBlock parent;
		final List<ConditionalBlock> children = new ArrayList<>();
		
		IPSTConditionalBlock node = null;
		
		// List of contained nodes that still need to be inserted, 
		// these lists will be modified during tree creation
		final List<ConditionalBlock> conditionalBlocks = new ArrayList<>();
		final List<IPSTIncludeDirective> includeDirectives = new ArrayList<>();
		final List<IPSTDirective> conditionalDirectives = new ArrayList<>();
		final List<IPSTDirective> otherDirectives = new ArrayList<>();
		
		ConditionalBlock(ConditionalBlock parent) {
			this.parent = parent;
		}
		
		@Override
		public int offset() {
			return node.offset();
		}
		
		@Override
		public int endOffset() {
			return node.endOffset();
		}
	}
	
	/**
	 * Create an intermediate tree that groups conditional preprocessor
	 * directives and the contained non-conditional directives into nodes.
	 * 
	 * @return root node containing preprocessor nodes located directly in the
	 *         translation unit file
	 * @throws UnbalancedConditionalDirectiveException
	 *             on unbalanced #if/#else/#endif directives
	 */
	private ConditionalBlock createConditionalBlockTree() {
		final ConditionalBlock root = new ConditionalBlock(null);
		ConditionalBlock head = root;
		
		for (IASTPreprocessorStatement statement : translationUnit.getAllPreprocessorStatements()) {
			// Skip all statements from included files
			final ISourceRange location = locationResolver.getSourceRangeInTranslationUnitFile(statement);
			if (location == null) {
				continue;
			}
			
			if (statement instanceof IASTPreprocessorIncludeStatement) {
				head.includeDirectives.add(
						nodeFactory.createIncludeDirective(location, (IASTPreprocessorIncludeStatement) statement));

			// Note that head == root should not be possible for #else and #endif directives,
			// because the parser seems to create problem nodes in these cases. 
			// However, unbalanced IASTPreprocessorIf*Statement do exist, even though they 
			// are not valid c.
			} else if (statement instanceof IASTPreprocessorIfStatement 
					|| statement instanceof IASTPreprocessorIfdefStatement
					|| statement instanceof IASTPreprocessorIfndefStatement) {
				ConditionalBlock newBlock = new ConditionalBlock(head);
				head = newBlock;
				head.conditionalDirectives.add(nodeFactory.createDirective(location, statement));
			} else if (statement instanceof IASTPreprocessorElseStatement
					|| statement instanceof IASTPreprocessorElifStatement) {
				if (head == root) {
					// should not happen
					throw new UnbalancedConditionalDirectiveException("freestanding " + statement + " at " + location);
				}
				head.conditionalDirectives.add(nodeFactory.createDirective(location, statement));
			} else if (statement instanceof IASTPreprocessorEndifStatement) {
				if (head == root) {
					// should not happen
					throw new UnbalancedConditionalDirectiveException("freestanding " + statement + " at " + location);
				}
				head.conditionalDirectives.add(nodeFactory.createDirective(location, statement));
				
				// block is complete, create real node and pop it off the stack
				head.node = createConditionalBlockNode(head.conditionalDirectives);
				head.parent.conditionalBlocks.add(head);
				
				head.parent.children.add(head);
				head = head.parent;
			} else {
				head.otherDirectives.add(nodeFactory.createDirective(location, statement));
			}
		}
		
		if (head != root) {
			// Does happen, but no compiler should accept this so a hard error
			// seems reasonable
			throw new UnbalancedConditionalDirectiveException("unterminated conditional directive "
					+ head.conditionalDirectives.get(head.conditionalDirectives.size() - 1));
		}

		return root;
	}
	
	
	private IPSTConditionalBlock createConditionalBlockNode(List<IPSTDirective> conditionalDirectives) {
		ISourceRange location = sourceDocument.newSourceRange(conditionalDirectives.get(0).offset(),
				conditionalDirectives.get(conditionalDirectives.size() - 1).endOffset());

		ISourceRange activeBranchLocation = null;
		for (int i = 0; i < conditionalDirectives.size() - 1; ++i) {
			if (ASTNodeUtils.isConditionalPreprocessorStatementTaken(conditionalDirectives.get(i).getASTNode())) {
				activeBranchLocation = sourceDocument.newSourceRange(conditionalDirectives.get(i).endOffset(),
						conditionalDirectives.get(i + 1).offset());
				break;
			}
		}

		return nodeFactory.createConditionalBlock(location, conditionalDirectives,
				activeBranchLocation);
	}
	
	
	
	

	static class CreateChildrenTask {
		final IPSTNode node;
		final List<IASTNode> children;
		final ConditionalBlock context;
		final CreateChildrenTask next;
		
		CreateChildrenTask(IPSTNode node, List<IASTNode> children, ConditionalBlock context, CreateChildrenTask next) {
			this.node = node;
			this.children = children;
			this.context = context;
			this.next = next;
		}
	}
	
	class TreeCreator {
		CreateChildrenTask stack = null;
		
		IPSTTranslationUnit create() {
			IPSTTranslationUnit root = nodeFactory.createTranslationUnit(
					locationResolver.getSourceRangeInTranslationUnitFile(translationUnit), translationUnit);	
			pushTask(root, Arrays.asList(translationUnit.getChildren()), conditionalBlockRoot);
			while (stack != null) {
				final CreateChildrenTask task = stack;
				stack = stack.next;
				groupOverlappingSiblings(task.children, task.context.conditionalBlocks,
						group -> createChildForGroup(task.node, group, task.context));
			}
			
			return root;
		}

		void pushTask(IPSTNode node, List<IASTNode> children, ConditionalBlock context) {
			stack = new CreateChildrenTask(node, children, context, stack);
		}
		
		void createChildForGroup(IPSTNode node, OverlappingSiblingsGroup group, ConditionalBlock context) {
			// Check if this is a conditional block
			if (group.firstConditionalBlockIndex != -1) {
				// There may be multiple expansions, check if the expanded location matches 
				// the block before creating a conditional block node for this group
				// If it doesn't there are overlapping nodes and/or multiple blocks
				final ConditionalBlock block = context.conditionalBlocks
						.get(group.firstConditionalBlockIndex);
				if (group.equalsSourceRange(block.node)) {
					context.conditionalBlocks.remove(group.firstConditionalBlockIndex);
					addConditionalBlock(node, group.nodes, block);
				} else {
					addOverlappingNode(node, group);
				}
				return;
			}
			
			// Check if it's an include
			int index = findEqualRange(context.includeDirectives, group);
			if (index != -1) {
				addPreprocessorNode(node, group.nodes, context.includeDirectives.remove(index));
				return;
			}
			
			// Check if it's a macro expansion
			// Certain macro expansions that cleanly map to astnodes may be added as regular nodes
			// with the macro expansion as only child
			index = findEqualRange(macroExpansions, group);			
			if (index != -1) {
				IPSTMacroExpansion macroExpansion = macroExpansions.remove(index);
				if (group.nodes.size() == 1 && treatMacroExpansionAsRegularNode(macroExpansion, group.nodes.get(0))) {
					addMacroExpansionAsRegularNode(node, macroExpansion, group.nodes.get(0));
					return;
				}

				addPreprocessorNode(node, group.nodes, macroExpansion);
				return;
			}
			
			// It's a regular node if there is only a single node at this location
			if (group.nodes.size() == 1) {
				addRegularNode(node, group, context);
				return;
			}
			
			// Otherwise group the nodes at this location into an overlapping block node
			// and just leave this mess alone
			addOverlappingNode(node, group);
		}

		void addConditionalBlock(IPSTNode parent, List<IASTNode> unexpandedChildren, ConditionalBlock block) {
			parent.addChild(block.node);
			if (expandConditionalBlocks) {
				pushTask(block.node, unexpandedChildren, block);
			} else {
				block.node.setUnexpandedChildNodes(unexpandedChildren);
			}
		}
		
		void addPreprocessorNode(IPSTNode parent, List<IASTNode> unexpandedChildren, IPSTNode node) {
			node.setUnexpandedChildNodes(unexpandedChildren);
			parent.addChild(node);
		}
		
		void addRegularNode(IPSTNode parent, OverlappingSiblingsGroup group, ConditionalBlock context) {
			final IASTNode astNode = group.nodes.get(0);
			final IPSTRegularNode node = nodeFactory.createRegularNode(group, astNode);
			parent.addChild(node);
			pushTask(node, Arrays.asList(astNode.getChildren()), context);
		}
		
		void addOverlappingNode(IPSTNode parent, OverlappingSiblingsGroup group) {
			final IPSTOverlappingRegion node = nodeFactory.createOverlappingRegion(group);
			node.setUnexpandedChildNodes(group.nodes);
			parent.addChild(node);
		}
		
		void addMacroExpansionAsRegularNode(IPSTNode parent, IPSTMacroExpansion macroExpansion, IASTNode astNode) {
			final IPSTRegularNode node = nodeFactory.createRegularNode(macroExpansion, astNode);
			parent.addChild(node);
			macroExpansion.setUnexpandedChildNodes(Arrays.asList(astNode.getChildren()));
			node.addChild(macroExpansion);
		}
		

	}
	
	
	/**
	 * A macro expansion that cleanly maps to a single ast-node is special,
	 * because it may still contain leading or trailing tokens that belong to
	 * the parent node.
	 * 
	 * This method decides if an ast-node that cleanly maps to a macro expansion
	 * is added as regular or macro expansions node.
	 * 
	 * @param expansion
	 * @param astNode
	 * @return true if the ast-node should be added as regular node
	 */
	protected boolean treatMacroExpansionAsRegularNode(IPSTMacroExpansion macroExpansion, IASTNode astNode) {
		// TODO: implement a better check for additional tokens and other potential problems
		// For now just check the macro definition text for a leading or trailing comma
		final String expansion = macroExpansion.getASTNode().getMacroDefinition().getExpansion();
		if (expansion.startsWith(",") || expansion.endsWith(",")) {
			return false;
		}
		
		return true;
	}
	
	/**
	 * Copy the original AST and group nodes if they are located in an included file, a macro expansion
	 * or a conditional preprocessor block. In cases where this is not possible, because AST
	 * and preprocessor node boundaries overlap, create an overlapping node to group problematic 
	 * source locations that cannot be simply rewritten. 
	 */
	private IPSTTranslationUnit createTree() {
		return new TreeCreator().create();
	}

	private static class OverlappingSiblingsGroup implements ISourceRange {
		final List<IASTNode> nodes = new ArrayList<>();
		int offset;
		int endOffset;
		int firstConditionalBlockIndex = -1;
		
		OverlappingSiblingsGroup(ISourceRange location) {
			this.offset = location.offset();
			this.endOffset = location.endOffset();
		}
		
		@Override
		public int offset() {
			return offset;
		}
		
		@Override
		public int endOffset() {
			return endOffset;
		}
	}
	
	
	/**
	 * Find siblings that overlap the same source location and thus cannot be
	 * added as siblings. The common case are macro expansions and includes, but
	 * this method also groups nodes within conditional preprocessor blocks in
	 * order to detect nodes that overlap #ifdef/#endif directives
	 * 
	 * @param siblings
	 * @param conditionalBlocks
	 * @param consumer
	 */
	private void groupOverlappingSiblings(List<IASTNode> siblings, List<? extends ISourceRange> conditionalBlocks,
			Consumer<OverlappingSiblingsGroup> consumer) {
		OverlappingSiblingsGroup currentGroup = null; 
		for (IASTNode node : siblings) {
			// Map the node location to the translation unit file and skip nodes that do not 
			// span any characters (e.g. implicit names)
			ISourceRange location = locationResolver.getSourceRangeMappedToInclusionStatement(node);
			if (location == null || location.length() == 0) {
				continue;
			}

			// Immediately add node to current group if it fits inside
			if (currentGroup != null && currentGroup.contains(location)) {
				currentGroup.nodes.add(node);
				continue;
			}
			
			// Expand the location to include enclosing conditional blocks
			int firstConditionalBlockIndex = -1;
			final IndexRange intersectedBlocks = findIntersectedRanges(conditionalBlocks, location);
			if (intersectedBlocks != null) {
				// Expand the location to include all blocks that have been found, 
				// but ignore fully contained blocks
				final ISourceRange expandedLocation = sourceDocument.newSourceRange(
						Math.min(location.offset(), conditionalBlocks.get(intersectedBlocks.first).offset()),
						Math.max(location.endOffset(), conditionalBlocks.get(intersectedBlocks.last).endOffset()));
				if (expandedLocation.offset() != location.offset()
						|| expandedLocation.endOffset() != location.endOffset()) {
					firstConditionalBlockIndex = intersectedBlocks.first;
					location = expandedLocation;
				}
			}
			
			if (currentGroup == null || location.offset() >= currentGroup.endOffset) {
				// Complete the current group and create a new one for this location
				if (currentGroup != null) {
					consumer.accept(currentGroup);
				}
				currentGroup = new OverlappingSiblingsGroup(location);
			} else {
				// Expand the current group
				currentGroup.endOffset = location.endOffset();
			}

			currentGroup.nodes.add(node);
			if (firstConditionalBlockIndex != -1 && currentGroup.firstConditionalBlockIndex == -1) {
				currentGroup.firstConditionalBlockIndex = firstConditionalBlockIndex;
			}
		}
		
		if (currentGroup != null) {
			consumer.accept(currentGroup);
		}
	}

	
	private void insertRemainingPreprocessorNodes(IPSTTranslationUnit root) {
		final List<IPSTNode> nodesToInsert = new ArrayList<>();
		collectRemainingPreprocessorNodes(conditionalBlockRoot, nodesToInsert);
		nodesToInsert.addAll(macroExpansions);
		nodesToInsert.addAll(comments);
		nodesToInsert.sort(HierarchicalSourceRangeComparator.getInstance());
		insertNodesNonRecursive(root, nodesToInsert);
	}
	
	private void collectRemainingPreprocessorNodes(ConditionalBlock block, List<IPSTNode> list) {
		block.conditionalBlocks.stream().map(c -> c.node).forEachOrdered(list::add);
		list.addAll(block.conditionalDirectives);
		list.addAll(block.otherDirectives);
		list.addAll(block.includeDirectives);
		for (ConditionalBlock child : block.children) {
			collectRemainingPreprocessorNodes(child, list);
		}
	}
	

	private static class InsertTask {
		static final int ENTER = 0;
		static final int CHILDREN = 1;
		static final int LEAVE = 2;

		final IPSTNode node;
		int state;
		int nextChildIndex;
		final InsertTask parentTask;

		InsertTask(IPSTNode node, int state, InsertTask parentTask) {
			this.node = node;
			this.state = state;
			this.nextChildIndex = 0;
			this.parentTask = parentTask;
		}
	}

	/**
	 * Perform a DFS traversal and insert nodes as deep as possible. Nodes are
	 * inserted recursively, i.e. nodes are inserted into previously inserted
	 * nodes if they fit. The given list of nodes to insert must be sorted
	 * hierarchically, i.e. by start offset and larger nodes come first on same
	 * offset.
	 * 
	 * @param root
	 *            node to start inserting nodes
	 * @param nodesToInsert
	 *            sorted list of nodes to insert, starting at root
	 */
	private void insertNodesNonRecursive(IPSTNode root, List<IPSTNode> nodesToInsert) {
		int nextInsertIndex = 0;
		final Deque<InsertTask> stack = new ArrayDeque<>();
		stack.push(new InsertTask(root, InsertTask.ENTER, null));
		while (!stack.isEmpty() && nextInsertIndex != nodesToInsert.size()) {
			final InsertTask task = stack.peek();

			// Insert next node as left sibling if it starts before this node
			// and immediately process it recursively before this node
			if (task.state == InsertTask.ENTER) {
				IPSTNode nextToInsert = nodesToInsert.get(nextInsertIndex);
				if (nextToInsert.offset() < task.node.offset()) {
					if (!skipInsertion(task.node.getParent(), nextToInsert)) {
						task.node.getParent().addChild(task.parentTask.nextChildIndex - 1, nextToInsert);
						++task.parentTask.nextChildIndex;
						stack.push(new InsertTask(nextToInsert, InsertTask.ENTER, task.parentTask));
					}
					++nextInsertIndex;
					continue;
				}

				task.state = InsertTask.CHILDREN;
			}
			
			// Enter next child of this node
			if (task.state == InsertTask.CHILDREN) {
				if (task.nextChildIndex < task.node.getChildren().size()) {
					stack.push(
							new InsertTask(task.node.getChildren().get(task.nextChildIndex), InsertTask.ENTER, task));
					++task.nextChildIndex;
					continue;
				}

				task.state = InsertTask.LEAVE;
			}
			
			// Add everything that ends within as new child
			if (task.state == InsertTask.LEAVE) {
				IPSTNode nextToInsert = nodesToInsert.get(nextInsertIndex);
				if (nextToInsert.endOffset() <= task.node.endOffset()) {
					if (!skipInsertion(task.node, nextToInsert)) {
						task.node.addChild(nextToInsert);
						stack.push(new InsertTask(nextToInsert, InsertTask.ENTER, task));
					}
					++nextInsertIndex;
					continue;
				}
				stack.pop();
			}
		}
	}
	
	/**
	 * Decides if a node is inserted into a certain parent node or not.
	 * Currently only called for preprocessor nodes that do not contain ast nodes.
	 * 
	 * @param parent
	 * @param node
	 * @return true node should not be inserted
	 */
	protected boolean skipInsertion(IPSTNode parent, IPSTNode node) {
		// Only allow insertion into the active branch
		if (parent instanceof IPSTConditionalBlock) {
			return !((IPSTConditionalBlock)parent).getActiveBranchLocation().contains(node);
		}
		
		return false;
	}
	

	private static class IndexRange {
		final int first; // inclusive 
		final int last; // inclusive 
		public IndexRange(int first, int last) {
			this.first = first;
			this.last = last;
		}
	}
	
	private static <T extends ISourceRange> IndexRange findIntersectedRanges(List<T> ranges, ISourceRange location) {
		// Find the first element that ends after the start offset,
		// all nodes before this one do not intersect
		int index = Collections.binarySearch(ranges, null,
				Comparator.comparingInt(o -> o == null ? location.offset() : o.endOffset()));
		index = (index < 0) ? -index - 1 : index + 1;

		// Find the first node that starts after the location
		int endIndex = index;
		for (; endIndex != ranges.size(); ++endIndex) {
			if (ranges.get(endIndex).offset() >= location.endOffset()) {
				break;
			}
		}
		return (index != endIndex) ? new IndexRange(index, endIndex - 1) : null;
	}
	
	private static <T extends ISourceRange> int findEqualRange(List<T> ranges, ISourceRange location) {
		final int index = Collections.binarySearch(ranges, location, Comparator.comparingInt(ISourceRange::offset));
		if (index >= 0 && ranges.get(index).endOffset() == location.endOffset()) {
			return index;
		}
		return -1;
	}
}
