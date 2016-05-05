from decimal import Decimal
import itertools
import sys

BOOL_QUERY_VAR = {}
DECISION_VAR_LIST = []


def is_number(s):
    try:
        float(s)
        return True
    except ValueError:
        return False


def pr_function(var, val, e, bn):
    parents = bn[var][0]
    if len(parents) == 0:
        true_prob = bn[var][1][None]
    else:
        parent_vals = [e[parent] for parent in parents]
        true_prob = bn[var][1][tuple(parent_vals)]
    if val == '+':
        return true_prob
    else:
        if var in DECISION_VAR_LIST:
            return 1.0
        return 1.0 - true_prob


def normalize(QX):
    total = 0.0
    for val in QX.values():
        total += val
    for key in QX.keys():
        QX[key] /= total
    return QX


def enumerate_all(all_vars, e,bn):
    if len(all_vars) == 0:
        return 1.0
    Y = all_vars.pop()
    if Y in e:
        val = pr_function(Y, e[Y], e, bn) * enumerate_all(all_vars, e, bn)
        all_vars.append(Y)
        return val
    else:
        total = 0
        e[Y] = '+'
        total += pr_function(Y, '+', e, bn) * enumerate_all(all_vars, e, bn)
        e[Y] = '-'
        total += pr_function(Y, '-', e, bn) * enumerate_all(all_vars, e, bn)
        del e[Y]
        all_vars.append(Y)
        return total


def enumeration_ask(X, e, bn, all_vars):
    distribution = {}
    for xi in ['-', '+']:
        e[X] = xi
        distribution[xi] = enumerate_all(all_vars, e, bn)
        del e[X]
    return normalize(distribution)


def read_file_data(file_handler):
    queries = []
    all_vars = []
    utility = []

    while True:
        query_str = str(file_handler.readline().rstrip())
        if query_str == "******":
            break
        queries.append(query_str)

    bayes_network = {}
    while True:
        line = str(file_handler.readline().rstrip())
        if line == "******" or line == '':
            break
        if line == "***":
            continue
        arr = line.split(' | ')
        if len(arr) > 1:
            key = arr[0]
            all_vars.insert(0, key)
            local_dict = {}
            parents = arr[1].split(' ')
            for i in range(2 ** len(parents)):
                bn_table_line = str(file_handler.readline().rstrip())
                bn_table_arr = bn_table_line.split(' ', 1)
                local_dict[tuple(bn_table_arr[1].split(' '))] = float(bn_table_arr[0])
            bayes_network[key] = [parents, local_dict]
        else:
            key = arr[0]
            all_vars.insert(0, key)
            local_dict = {}
            prob_value = file_handler.readline().rstrip('\r\n')
            if is_number(prob_value):
                local_dict[None] = float(prob_value)
            else:
                DECISION_VAR_LIST.append(key)
                local_dict[None] = 1.0
            bayes_network[key] = [[], local_dict]

    while True:
        line = str(file_handler.readline().rstrip())
        if line == '':
            break
        arr = line.split(' | ')
        if len(arr) > 1:
            another_local_dict = {}
            util_dependency_nodes = arr[1].split(' ')
            utility.append(util_dependency_nodes)
            for i in range(2 ** len(util_dependency_nodes)):
                util_val_line = str(file_handler.readline().rstrip())
                util_val_arr = util_val_line.split(' ', 1)
                another_local_dict[tuple(util_val_arr[1].split(' '))] = float(util_val_arr[0])
            utility.append(another_local_dict)

    return queries, bayes_network, utility, all_vars


def generate_enum_params(query):
    global BOOL_QUERY_VAR
    BOOL_QUERY_VAR = {}
    query_vars_list = []
    events_dict = {}
    statement = query[query.find("(") + 1:query.find(")")]
    statement_arr = statement.split(" | ")
    question_arr = statement_arr[0].split(", ")

    for ques in question_arr:
        var = ques.split(" = ")
        query_vars_list.append(var[0])
        if(len(var) > 1):
            BOOL_QUERY_VAR[var[0]] = var[1]

    if len(statement_arr) > 1:
        event_list = statement_arr[1].split(", ")
        for event in event_list:
            var_bool_pair = event.split(" = ")
            events_dict[var_bool_pair[0]] = var_bool_pair[1]
            BOOL_QUERY_VAR[var_bool_pair[0]] = var_bool_pair[1]

    return query_vars_list, events_dict


def get_probability_array(query_list, sign_tuple, evidence_dict, bn, all_vars):
    prob_arr = []
    num_query = len(query_list)
    i = 0
    if num_query == 1:
        result_dict = enumeration_ask(query_list[0], evidence_dict, bn, all_vars)
        if sign_tuple[0] == '+':
            prob_arr.append(result_dict['+'])
        else:
            prob_arr.append(result_dict['-'])

    elif num_query > 1 and not bool(evidence_dict) :
        for ele in query_list:
            if i >= num_query:
                break
            temp_dict = {}
            for item in query_list[i + 1:]:
                temp_dict[item] = BOOL_QUERY_VAR[item]
            result_dict = enumeration_ask(ele, temp_dict, bn, all_vars)
            if sign_tuple[i] == '+':
                prob_arr.append(result_dict['+'])
            else:
                prob_arr.append(result_dict['-'])
            i += 1

    else:
        temp_bool_vars = BOOL_QUERY_VAR
        k = 0
        for component in query_list:
            temp_bool_vars[component] = sign_tuple[k]
            k += 1
        temp_query_list = query_list + list(evidence_dict.keys())
        for ele in temp_query_list:
            if i >= num_query:
                break
            temp_dict = {}
            for item in temp_query_list[i + 1:]:
                temp_dict[item] = temp_bool_vars[item]
            result_dict = enumeration_ask(ele, temp_dict, bn, all_vars)
            if sign_tuple[i] == '+':
                prob_arr.append(result_dict['+'])
            else:
                prob_arr.append(result_dict['-'])
            i += 1

    return prob_arr


def get_probability_value(prob_arr):
    probability = 1
    for val in prob_arr:
        probability *= val
    return probability


def main():
    global BOOL_QUERY_VAR
    logger_count = 0
    input_file_handler = open("sample01.txt", 'r')
    output_file_handler = open("output.txt", 'w')
    logger = ""
    given_queries, bayes_network, utility_network, all_variables = read_file_data(input_file_handler)
    for query in given_queries:
        if query[0] == 'P':
            sign_tuple = ()
            query_list, event_dict = generate_enum_params(query)
            for var in query_list:
                sign_tuple += (BOOL_QUERY_VAR[var],)
            prob_arr = get_probability_array(query_list, sign_tuple, event_dict, bayes_network, all_variables)
            probability = get_probability_value(prob_arr)
            logger += str(Decimal(str(probability + 1e-8)).quantize(Decimal('.01')))
            logger_count += 1
            if logger_count < len(given_queries):
                logger += "\n"

        elif query[0] == 'E':
            eu_answer = 0
            unset_decision_list, evidence_dict = generate_enum_params(query)
            new_query_var_list = []
            req_decision_list = []
            for unset_decision in unset_decision_list:
                evidence_dict[unset_decision] = BOOL_QUERY_VAR[unset_decision]
            for ele in utility_network[0]:
                if ele not in DECISION_VAR_LIST:
                    new_query_var_list.append(ele)
                else:
                    req_decision_list.append(ele)
            tuple_list = list(itertools.product(('+', '-'), repeat=len(new_query_var_list)))

            eu_arr = []
            for tup in tuple_list:
                hack_dict = {}
                for z in range(0, len(tup)):
                    hack_dict[new_query_var_list[z]] = tup[z]
                new_tuple = ()
                prob_arr = get_probability_array(new_query_var_list, tup, evidence_dict, bayes_network, all_variables)
                probability = get_probability_value(prob_arr)
                for each in req_decision_list:
                    hack_dict[each] = BOOL_QUERY_VAR[each]
                for y in utility_network[0]:
                    new_tuple += (hack_dict[y],)
                eu_arr.append(probability * utility_network[1][new_tuple])
            for num in eu_arr:
                eu_answer += num

            Decimal(str(eu_answer)).quantize(Decimal('.01'))
            logger += str(Decimal(str(eu_answer + 1e-8)).quantize(Decimal('1.')))
            logger_count += 1
            if logger_count < len(given_queries):
                logger += "\n"


        elif query[0] == 'M':
            meu_answer = []
            unset_decision_list, evidence_dict = generate_enum_params(query)
            eu_tuples = list(itertools.product(('+', '-'), repeat=len(unset_decision_list)))
            for every_tup in eu_tuples:
                new_query_var_list = []
                req_decision_list = []
                eu_answer = 0
                for ele in utility_network[0]:
                    if ele not in DECISION_VAR_LIST:
                        new_query_var_list.append(ele)
                    else:
                        req_decision_list.append(ele)

                j = 0
                for unset_decision in unset_decision_list:
                    evidence_dict[unset_decision] = every_tup[j]
                    BOOL_QUERY_VAR[unset_decision] = every_tup[j]
                    j += 1
                tuple_list = list(itertools.product(('+', '-'), repeat=len(new_query_var_list)))
                eu_arr = []
                for tup in tuple_list:
                    hack_dict = {}
                    for z in range(0, len(tup)):
                        hack_dict[new_query_var_list[z]] = tup[z]
                    new_tuple = ()
                    prob_arr = get_probability_array(new_query_var_list, tup, evidence_dict, bayes_network, all_variables)
                    probability = get_probability_value(prob_arr)

                    for each in req_decision_list:
                        hack_dict[each] = evidence_dict[each]

                    for y in utility_network[0]:
                        new_tuple += (hack_dict[y],)
                    eu_arr.append(probability * utility_network[1][new_tuple])
                for num in eu_arr:
                    eu_answer += num
                meu_answer.append(eu_answer + 1e-8)

            result_list = list(eu_tuples[meu_answer.index(max(meu_answer))])
            res_str = ""
            for every_ele in result_list:
                res_str += every_ele + " "

            logger += res_str + str(Decimal(str(max(meu_answer))).quantize(Decimal('1.')))
            logger_count += 1
            if logger_count < len(given_queries):
                logger += "\n"

    output_file_handler.write(logger)
    output_file_handler.close()
    input_file_handler.close()

if __name__ == '__main__':
    main()
