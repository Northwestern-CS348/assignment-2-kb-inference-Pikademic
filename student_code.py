import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:  #fact not already in self.facts
                self.facts.append(fact_rule)   #adds the fact to fact list
                for rule in self.rules: #for every rule, infers (fact, rules in list)
                    self.ie.fc_infer(fact_rule, rule, self)
            else: #fact already in self.facts
                if fact_rule.supported_by: #if input fact has support from other facts/rules
                    ind = self.facts.index(fact_rule) #obtains index of the fact
                    for f in fact_rule.supported_by: #adds support from added fact to existing fact
                        self.facts[ind].supported_by.append(f)
                else: #unsupported input fact
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True #if no supports must be asserted directly
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here
        #
        # Problem: Removing rules and facts inferred from a removed fact
        #   When you remove a fact, you also need to remove all facts and rules that were inferred using this fact.
        #   However, a given fact/rule might be supported by multiple facts - so, you'll need to check whether the facts/rules inferred
        #   from this fact are also supported by other facts (or if they were directly asserted).
        #
        #[Cases]
        #   1. Removing a Fact
        #       1a. Remove all facts and rules inferred from this fact that are now unsupported since the input fact was removed
        #           - Don't remove directly asserted facts unless they are the input for retract
        #   2. Removing a Rule
        #       2a. You cannot remove an asserted rule, only assumed rules without any support
        #       2b. Remove all facts and rules inferred from this rule that are now unsupported since the input rule was removed

        #Case 0: fact_or_rule input Fact or Rule is not contained in the kb, returns immediately
        if (fact_or_rule not in self.rules) and (fact_or_rule not in self.facts):
            print('Input not in knowledgebase. Exiting function.')
            return 


        #Case 1: Removing a Fact
        if isinstance(fact_or_rule, Fact):
            fac = self._get_fact(fact_or_rule)
            #Removes asserted tag if applicable
            fac.asserted = False
            #Checks if this fact is supported by any other facts/rules.  If so does nothing further as it is an inferred fact.
            if fac.supported_by:
                return 
            #If it is not supported by anything, then this fact is going to be removed, and each fact/rule that it supported should be
            #checked for removal as well if they end up being unsupported/unasserted
            else:
                #Removes the input Fact from the knowledgebase
                self.facts.remove(fact_or_rule)
                #Checks Facts that input supports for removal
                for sup_fact in fac.supports_facts:
                    #Remove input from sup_fact.supported_by array
                    for pair in sup_fact.supported_by:
                        if fac in pair:
                            sup_fact.supported_by.remove(pair)

                    #If the sup_fact is now without any supports and is not asserted, it will also be retracted.
                    if (len(sup_fact.supported_by) == 0) and (sup_fact.asserted == False):
                        self.kb_retract(sup_fact)

                #Checks Rules that input supports for removal
                for sup_rules in fac.supports_rules:
                    #Remove input from sup_rules.supported_by array
                    for pair in sup_rules.supported_by:
                        if fac in pair:
                            sup_rules.supported_by.remove(pair)                    

                    #If the sup_rule is now without any supports and is not asserted, it will also be retracted.
                    if (len(sup_rules.supported_by) == 0) and (sup_rules.asserted == False):
                        self.kb_retract(sup_rules)



        #Case 2: Removing a Rule
        elif isinstance(fact_or_rule, Rule):
            rul = self._get_rule(fact_or_rule)
            #If the rule is asserted immediately exits and does nothing
            if rul.asserted:
                return 
            #If the rule is supported by anything does nothing further as it is an inferred rule
            if rul.supported_by:
                return 
            #If the rule is neither asserted or supported, it will be removed and each fact/rule that it supported should be
            #checked for removal as well if they end up being unsupported/unasserted
            else:
                #Removes the input Fact from the knowledgebase
                self.rules.remove(fact_or_rule)
                #Checks Facts that input supports for removal
                for sup_fact in rul.supports_facts:
                    #Remove input from sup_fact.supported_by array
                    for pair in sup_fact.supported_by:
                        if rul in pair:
                            sup_fact.supported_by.remove(pair)
                    #If the sup_fact is now without any supports and is not asserted, it will also be retracted.
                    if (len(sup_fact.supported_by) == 0) and (sup_fact.asserted == False):
                        self.kb_retract(sup_fact)

                #Checks Rules that input supports for removal
                for sup_rules in rul.supports_rules:
                    #Remove input from sup_rules.supported_by array
                    for pair in sup_rules.supported_by:
                        if rul in pair:
                            sup_rules.supported_by.remove(pair) 
                    #If the sup_rule is now without any supports and is not asserted, it will also be retracted.
                    if (len(sup_rules.supported_by) == 0) and (sup_rules.asserted == False):
                        self.kb_retract(sup_rules)








class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        #
        # Pseudocode:
        #  [Fact]
        #  1. When a new fact is added check to see if it triggers any rules
        #      - Use [match(state1, state2, bindings=None) ((Statement, Statement, Bindings) => Bindings|False)]
        #  2.  Check the [first element of the LHS of every rule in the knowledge base] against this [new fact]
        #       "Every X in knowledge base" is implemented in kb_add
        #  3.  If there is a match with this element to a fact in the KB, add a new rule paired with bindings for that match
        #
        # [Rule]
        #   1. When a new rule is added check to see if it is triggered by existing facts
        #   2. Check the [first element of the LHS of this new rule] against the [facts in the KB]
        #   3. If there is a match with this element to a fact in the KB, add a new rule paired with bindings for that match
        #
        # [Cases]
        #   - If the lhs of the rule only has 1 element and match is successful, asserts a fact based on the RHS of the rule
        #   - If the lhs of the rule contains more than 1 element, generates a new rule eliminating the first element if a match is successful

        #Obtain the first Statement within the input rule's LHS (listof Statement)
        first_statement = rule.lhs[0]

        #Check to see if this first_statement matches the input fact
        matched_binding = match(first_statement, fact.statement)

        #If the binding exists, will not be false
        if matched_binding:
            #instantiate function will generate a new statement from bindings with bound values for variables if exist within bindings
            #In this case converts a fact statement and a binding into a condensed statement
            #   - fact: (somePredicate ?x ?y)
            #   - (?x : A, ?y : B)
            #  Into this one thing
            #   - fact: (somePredicate A B)
            #
            #Example:
            #If given [rule ((sizeIsLess(?y, ?x), on(?x, ?y)) => covered(?y))] and [fact sizeIsLess(B, A)]
            #   - match of first element: match(sizeIsLess(?y, ?x), sizeIsLess(B,A)) => the matching ((?x: A, ?y: B))
            #
            #Instantiate will then take in a fact statement and bindings and create a new fact statement
            #   - Inputs:
            #       - statement: sizeIsLess(?y, ?x)
            #       - bindings:  ((?x: A, ?y: B))
            #   - Output:
            #       - statement: sizeIsLess(A, B)

            #Case One: len(rule.lhs) = 1, a fact can be inferred from instantiating the rhs of the rule.
            if len(rule.lhs) == 1:
                # A fact contains a String name, Statement statement, array of Facts/Rules supported_by, and individual arrays of Facts
                # supports_facts, and Rules support_rules
                # init requires only a Statement, and an array of supported Facts/Rules
                new_fact_statement = instantiate(rule.rhs, matched_binding)
                supports = [(fact, rule)] #inputs
                new_fact = Fact(new_fact_statement, supports)
                # inputs are also supported by this new fact
                fact.supports_facts.append(new_fact)
                rule.supports_facts.append(new_fact)
                # new_fact is an inferred fact.
                kb.kb_assert(new_fact)

            #Case Two: len(rule.lhs) > 1, a new rule can be inferred from rule, eliminating the first element if a match is successful
            elif len(rule.lhs) > 1:
                #Create a new lhs of type (listof Statement) containing every element of rule.lhs other than the first, which matched with the input fact
                lhs_exclude_first = []
                #Array slicing will return every element after the first
                for statements in rule.lhs[1:]:
                    #Create rule statements with the bindings in place
                    lhs_exclude_first.append(instantiate(statements, matched_binding))
                #Create new rule based on this new LHS
                supports = [(fact, rule)] #inputs
                rhs = instantiate(rule.rhs, matched_binding) 
                new_rule = Rule([lhs_exclude_first, rhs], supports)
                # inputs are also supported by this new rule
                fact.supports_facts.append(new_rule)
                rule.supports_facts.append(new_rule)
                # new_fact is an inferred fact.
                kb.kb_assert(new_rule)
            else:
                #Something went wrong if length is 0 or less than that
                print('Something went wrong with inferring')












