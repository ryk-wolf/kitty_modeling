#Model for kitty


####################
##     SETS      ##
####################
set PEOPLE; #The people who participate in the kitty
set GIFTS;  #The gifts bought with the kitty



####################
## RAW PARAMETERS ##
####################
/*  [Euros, in total] The maximum amount allowed for a transaction,
here fixed at 180*/
param max_transaction_amount >= 0;

/* [Euros, per person per gift] The amount each person spent on each gift */
param amount_spent_on_gifts_by_each {PEOPLE, GIFTS} >=0 ;

/* [Boolean, binary] The people who spent an amount of money on each gift */
param pers_who_bought_each_gift {PEOPLE, GIFTS} binary >= 0;

/* [Boolean, binary] The people who participated in buying each gift
 ("de la part de") */
param pers_giving_each_gift {PEOPLE, GIFTS} binary >= 0;

/*  [Euros, singleton] The maximal difference allowed between
what two participants spend*/
param fixed_epsilon >= 0;





#####################
#COMPUTED PARAMETERS#
#####################
/* [Euros-int, per person]  The initial amount spent by the person when buying
the gift, before any equalisation transactions are made */
param initial_amount_spent_on_gifts {p in PEOPLE} =
  sum {g in GIFTS} amount_spent_on_gifts_by_each[p, g];

/*  [Euros-int, per gift]   The price of each gift*/
param gift_price {g in GIFTS} =
  sum {p in PEOPLE} amount_spent_on_gifts_by_each[p,g];

/*  [Euros-int, per person] The sum of the prices of the gifts
to which the person has participated.
Example: if A and B buy a gift worth 10 and A and C buy a gift worth 30
then max_... for A =10+30=40, B = 10, C = 30*/
param max_amount_spent_on_participated_gifts {p in PEOPLE} =
  sum {g in GIFTS} gift_price[g] * pers_giving_each_gift[p, g];



####################
##  RAW VARIABLES ##
####################
/* [Euros-int, per person] The amount p0 gives to p1 */
var transaction_amount {PEOPLE, PEOPLE} integer >= 0;




######################
# COMPUTED VARIABLES #
######################
/* [Euros-int, per person]  The total amount of money received by that person */
var total_amount_received {PEOPLE} >= 0;
subject to total_amount_received_by_a_person_from_all_others {p0 in PEOPLE}:
  total_amount_received[p0] =
  sum {p1 in PEOPLE} transaction_amount[p1, p0];

/* [Euros-int, per person]  The total amount of money given by that person */
var total_amount_given {PEOPLE} >= 0;
subject to total_amount_given_by_a_person_to_all_others {p0 in PEOPLE}:
  total_amount_given[p0] =
  sum {p1 in PEOPLE} transaction_amount[p0, p1];

/* [Euros-int, per person] The final total amount a person will have spent
in the kitty, in the end, taking into account how much was given back
to them and how much they gave to others */
var final_total_amount {PEOPLE} >= 0;
subject to final_total_amount_spent_in_kitty_by_each_person {p in PEOPLE}:
  final_total_amount[p] =
  initial_amount_spent_on_gifts[p] + total_amount_given[p] - total_amount_received[p];

/* [Euros-int, in general] The general difference between the amounts
each participant is paying */
var epsilon >= 0;
subject to epsilon_upper_bound {p in PEOPLE}: - epsilon <= final_total_amount[p];
subject to epsilon_lower_bound {p in PEOPLE}: final_total_amount[p] <= epsilon;

/*  [Boolean, binary] Whether an exchange took place between two people
  1 corresponds to truth, meaning there has been an exchange between both people,
  0 corresponds to false and therefore no exchange between both*/
var is_an_exchange {PEOPLE, PEOPLE} binary >= 0;
subject to exchange_TRUE {p0 in PEOPLE, p1 in PEOPLE}:    #case 1
  is_an_exchange[p0,p1] >= transaction_amount[p0,p1]/max_transaction_amount;
subject to exchange_FALSE {p0 in PEOPLE, p1 in PEOPLE}:   #case 0
  is_an_exchange[p0,p1] <= transaction_amount[p0,p1];

/*  [Integer, total] The number of exchanges between each two participants*/
var exchanges_counter integer >= 0;
subject to total_number_of_exchanges:
  exchanges_counter = sum {p0 in PEOPLE, p1 in PEOPLE} is_an_exchange[p0,p1];

/*  [Euros-real, in general] Transforming fairness objective into constraints*/
var highest_spending >= 0;
var lowest_spending >= 0;
subject to highest_spending_definition {p in PEOPLE}:
  final_total_amount[p] <= highest_spending;
subject to lowest_spending_definition {p in PEOPLE}:
  final_total_amount[p] >= lowest_spending;



####################
##   CONSTRAINTS  ##
####################
/* No transaction amount between two people can exceed
max_transaction_amount (here 180) euros */
subject to max_amount_by_transaction {p0 in PEOPLE, p1 in PEOPLE}:
  transaction_amount[p0, p1] <= max_transaction_amount;

/* Person A (Avare~greedy) doesn't wish to receive any money from others */
subject to greedy_shall_not_receive_money {p in PEOPLE}:
  transaction_amount[p, "A"] == 0;

/* No one should give themselves money, since it does not make sense */
subject to no_one_should_refund_themselves {p in PEOPLE}:
  transaction_amount[p, p] == 0;

/* Amounts spent by two participants should be as close as possible,
at an epsilon difference */
subject to fairness_rule {p0 in PEOPLE, p1 in PEOPLE}:
  final_total_amount[p0] - final_total_amount[p1] <= epsilon;

/* Amount spent by a participant can't be superior to
the sum of the prices of the gifts to which he has participated*/
subject to cant_spend_more_than_sum_of_participated_gifts_costs {p in PEOPLE}:
  final_total_amount[p] <= max_amount_spent_on_participated_gifts[p];

/*  The total sum of all participant's spending must be equal to the conjugated
price of all gifts*/
subject to sum_of_all_spent_amounts_cant_be_more_than_total_gifts_costs:
sum {p in PEOPLE} final_total_amount[p] = sum {p in PEOPLE} initial_amount_spent_on_gifts[p];

/*The constraint corresponding to the former minimizing unfairness objective*/
subject to maintain_fairness:
  highest_spending - lowest_spending <= fixed_epsilon;




####################
##    OBJECTIVE   ##
####################
/*Phony objective for exercise 1*/
maximize phony:   1;

/* Fairness rule, minimizing computed var epsilon which stands for
the difference between two amounts paid */
minimize unfairness:    epsilon;

/* The total number of transactions between Participants, corresponds to
exercise 3 and onwards */
minimize number_of_transactions:
  exchanges_counter;
