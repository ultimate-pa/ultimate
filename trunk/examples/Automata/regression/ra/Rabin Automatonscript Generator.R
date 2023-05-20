# Generate an mxnxn semi-random adjacency matrix

#variables:

seed <- 7 # set the seed for reproducibility
n <- 100 #states
m <- 5 #alphabet characters
p <- 0.01 #probability for two states having a transition per character
pF <- 0.3 #probability for a state to be finite (overwritten by final states)
pA <- 0.05 #propability for state to be accepting, if not >=0 & <=1, s_n is default
pS <- 0.1 #propability for state to be a valid start, if not >=0 & <=1, s_1 is the default

filename <- paste(seed,n,m,p,pF,pA,paste0(pS,".ats"), sep = "-") #(variable values are in the same order as given in filename)




#functions:
set.seed(seed)
generate_adj_matrix <- function(n, p, m) {
  adj_matrix <- array(dim = c(m,n,n), data =sample(c(0, 1), m*n*n, replace = TRUE, prob = c(1-p, p)))
  adj_matrix
}

adj_matrix <- generate_adj_matrix(n, p, m)



#adjecency-matrix to .ats (transitions)
generate_transitions <- function(adj_matrix) {
  transitions <- character()
  for (i in 1:m) {
    for (j in 1:n) {
      for(k in 1:n){
        if (adj_matrix[i,j,k] != 0) {
          transition <- sprintf("(s%d t%d s%d)", j, i, k)
          transitions <- c(transitions, transition)
        }
      }
    }
  }
  transitions
}

#generates finite/accepting/starting states

if(((0<=pF) && (pF<=1)) && !is.nan(pF)){
finite_Array <- array(dim = c(n), data = sample(c(0, 1), n, replace = TRUE, prob = c(1-pF,pF)))
}else{
  finite_Array <- array(dim = c(n), data = 0)
}

if(((0<=pA) && (pA<=1)) && !is.nan(pA)){
  accepting_Array <- array(dim = c(n), data = sample(c(0, 1), n, replace = TRUE, prob = c(1-pA,pA)))
}else{
  accepting_Array <- array(dim = c(n), data = 0)
  accepting_Array[n] <- 1
}
finite_Array <- finite_Array & !accepting_Array #accepting states shouldn't be finite

if(((0<=pS) && (pS<=1)) && !is.nan(pS)){
  starting_Array <- array(dim = c(n), data = sample(c(0, 1), n, replace = TRUE, prob = c(1-pS,pS)))
}else{
  starting_Array <- array(dim = c(n), data = 0)
  starting_Array[1] <- 1
}


generate_state_list <- function(stateArray) {
  result <- character()
  for(i in 1:n){
    if (stateArray[i] != 0) {
      newState <- sprintf("s%d", i)
      result <- c(result, newState)
    }
  }
  result
}

# Define the automaton as a list
automaton <- list(
  alphabet = character(),
  states = character(),
  initialStates = generate_state_list(starting_Array),
  acceptingStates = generate_state_list(accepting_Array), 
  finiteStates = generate_state_list(finite_Array),
  transitions = generate_transitions(adj_matrix)
)

# Extract alphabet from transitions
automaton$alphabet <- unique(gsub(".*\\s(\\S+)\\s.*", "\\1", automaton$transitions))

# Extract states from transitions and other state lists
all_states <- unique(c(automaton$initialStates, automaton$acceptingStates, automaton$finiteStates,
                       unlist(strsplit(gsub("[()]", "", automaton$transitions), " "))[c(TRUE, FALSE, TRUE)]))
automaton$states <- unique(unlist(strsplit(all_states, " ")))


# Create a String and append the automaton definition

result <- paste0("RabinAutomaton automaton = (\n",
"\talphabet = {", paste(automaton$alphabet, collapse = " "), "},\n",
"\tstates = {", paste(automaton$states, collapse = " "),"},\n",
"\tinitialStates = {", paste(automaton$initialStates, collapse = " "), "},\n",
"\tacceptingStates = {", paste(automaton$acceptingStates, collapse = " "), "},\n",
"\tfiniteStates = {", paste(automaton$finiteStates, collapse = " "), "},\n",
"\ttransitions = { ")
for (i in 1:length(automaton$transitions)) {
  result <- paste0(result,automaton$transitions[i])
  if (i != length(automaton$transitions)) {
    result <- paste0(result," ")
  }
}
result <- paste0(result," }\n);")
#result <- paste0(result,"\n\nassert(isEmpty(automaton));")


# Write the final string to a file
fileConn <- file(filename)
writeLines(result, fileConn)
close(fileConn)













#Rabin Visualizer
library(DiagrammeR)
#labels that could be used for visualisation, currently not used
labels <- rep()
for (i in 1:max(m,n)) {
  if (i <= 26) {
    labels[i] <- intToUtf8(64 + i) # A-Z
  } else if (i <= 52) {
    labels[i] <- intToUtf8(70 + i) # a-z
  } else {
    labels[i] <- paste0(labels[floor(i/52)], labels[((i-1) %% 52) + 1]) # AA, AB, AC, ..., BA, BB, BC, ...
  }
}

# Create mermaid header for the graph
mermaid_code <- "graph TD;\n\n"

# Add nodes style to the code
#mermaid_code <- paste0(mermaid_code, "START[\" \"]-->", 1,";\nstyle START stroke-width: 0, fill:#ffffff;\n")#start edge
for (i in 1:n) {
  node_label <- paste0("((", "s", i, "));\n")
  if(finite_Array[i] != 0){
    node_label <- paste0(node_label, "style ",i," stroke:#000000 ,stroke-dasharray:3;\n")
  }
  if(starting_Array[i] != 0){
    mermaid_code <- paste0(mermaid_code, "START", i, "[\" \"]-->", i,";\nstyle START", i, " stroke-width: 0, fill:#000000;\n")#start edge
  }
  if(accepting_Array[i] != 0){
    mermaid_code <- paste0(mermaid_code, "style ", i, " stroke-width: 2,stroke:#000000 ,fill:#ff0000;\n")
  }
  
  mermaid_code <- paste0(mermaid_code, i, node_label)
}


# Add edges to the code
for (i in 1:m) {
  for (j in 1:n) {
    for (k in 1:n) {
      if (adj_matrix[i,j,k] == 1) {
        mermaid_code <- paste0(mermaid_code, j,"--", "t", i, "-->", k, ";\n")
      }
    }
  }
}

# Generate the graph from the mermaid code
mermaid(mermaid_code, width = 4000, height = 4000)

# debug: cat(mermaid_code)