/* Comparison of Incorrect vs Correct Dynamic BCRA Formulas
 * For analysis and modeling purposes
 * 
 * INCORRECT FORMULA (Sum-based):
 * CA(t) = max(10, min(C_max, C_base × Σ_{i∈active} g(p_i, E_i) × Π_nash))
 * 
 * CORRECT FORMULA (Exponential Product-based):
 * CA(t) = min(C_max, C_base × exp(∏_{i∈active} g(p_i, E_i)) × Π_nash)
 */

#include <stdio.h>
#include <math.h>
#include <stdlib.h>

/* Constants */
#define K1 1.5      /* Linear scaling factor */
#define K2 2.0      /* Exponential scaling factor */
#define MIN_COST 10.0  /* Only used in incorrect formula */

/* Nash equilibrium weights */
#define W1 0.3      /* Equilibrium factor weight */
#define W2 0.2      /* Competition factor weight */
#define W3 0.2      /* Reputation factor weight */
#define W4 0.15     /* Bayesian factor weight */
#define W5 0.15     /* Signaling factor weight */

typedef struct {
    double threat_probability;      /* p_i: [0,1] */
    double defense_effectiveness;   /* E_i: [0,1] */
} threat_t;

typedef struct {
    double equilibrium_factor;
    double competition_factor;
    double reputation_factor;
    double bayesian_factor;
    double signaling_factor;
} nash_components_t;

/* Growth function: g(p_i, E_i) = 1 + k1 * p_i * (2 - E_i)^k2 */
double growth_function(double p, double E) {
    return 1.0 + K1 * p * pow(2.0 - E, K2);
}

/* Nash equilibrium multiplier */
double nash_multiplier(nash_components_t *nash) {
    return W1 * nash->equilibrium_factor +
           W2 * nash->competition_factor +
           W3 * nash->reputation_factor +
           W4 * nash->bayesian_factor +
           W5 * nash->signaling_factor;
}

/* INCORRECT FORMULA - Sum of growth functions */
double incorrect_threat_sum(threat_t *threats, int num_threats) {
    double sum = 0.0;
    for (int i = 0; i < num_threats; i++) {
        sum += growth_function(threats[i].threat_probability,
                             threats[i].defense_effectiveness);
    }
    return sum;
}

double incorrect_dynamic_bcra(double base_cost, double max_cost,
                             threat_t *threats, int num_threats,
                             nash_components_t *nash) {
    /* INCORRECT: Uses sum of growth functions */
    double threat_component = incorrect_threat_sum(threats, num_threats);
    double nash_component = nash_multiplier(nash);
    
    /* Linear scaling with sum */
    double raw_cost = base_cost * threat_component * nash_component;
    
    /* Apply bounds with minimum */
    double bounded_cost = fmin(max_cost, raw_cost);
    return fmax(MIN_COST, bounded_cost);
}

/* CORRECT FORMULA - Product of growth functions with exponential */
double correct_threat_product(threat_t *threats, int num_threats) {
    double product = 1.0;
    for (int i = 0; i < num_threats; i++) {
        product *= growth_function(threats[i].threat_probability,
                                 threats[i].defense_effectiveness);
    }
    return product;
}

double correct_dynamic_bcra(double base_cost, double max_cost,
                          threat_t *threats, int num_threats,
                          nash_components_t *nash) {
    /* CORRECT: Uses product of growth functions */
    double threat_component = correct_threat_product(threats, num_threats);
    double nash_component = nash_multiplier(nash);
    
    /* Exponential scaling with product */
    double raw_cost = base_cost * exp(threat_component) * nash_component;
    
    /* Apply upper bound only (no minimum) */
    return fmin(max_cost, raw_cost);
}

/* Analysis helper - shows the difference in behavior */
void analyze_formulas() {
    double base_cost = 100.0;
    double max_cost = 2000.0;
    
    /* Nash components (neutral values) */
    nash_components_t nash = {
        .equilibrium_factor = 1.0,
        .competition_factor = 1.0,
        .reputation_factor = 1.0,
        .bayesian_factor = 1.0,
        .signaling_factor = 1.0
    };
    
    printf("Formula Comparison Analysis\n");
    printf("==========================\n\n");
    
    /* Test Case 1: No threats */
    printf("Test Case 1: No threats\n");
    threat_t no_threats[0];
    double incorrect_result = incorrect_dynamic_bcra(base_cost, max_cost, no_threats, 0, &nash);
    double correct_result = correct_dynamic_bcra(base_cost, max_cost, no_threats, 0, &nash);
    printf("  Incorrect formula: %.2f\n", incorrect_result);
    printf("  Correct formula:   %.2f\n", correct_result);
    printf("  Difference:        %.2f\n\n", correct_result - incorrect_result);
    
    /* Test Case 2: Single low threat */
    printf("Test Case 2: Single low threat (p=0.2, E=0.8)\n");
    threat_t low_threat[] = {{0.2, 0.8}};
    incorrect_result = incorrect_dynamic_bcra(base_cost, max_cost, low_threat, 1, &nash);
    correct_result = correct_dynamic_bcra(base_cost, max_cost, low_threat, 1, &nash);
    printf("  Growth function g(0.2, 0.8) = %.4f\n", growth_function(0.2, 0.8));
    printf("  Incorrect formula: %.2f\n", incorrect_result);
    printf("  Correct formula:   %.2f\n", correct_result);
    printf("  Difference:        %.2f\n\n", correct_result - incorrect_result);
    
    /* Test Case 3: Multiple moderate threats */
    printf("Test Case 3: Multiple moderate threats\n");
    threat_t moderate_threats[] = {
        {0.3, 0.7},  /* 30% probability, 70% defense */
        {0.5, 0.5},  /* 50% probability, 50% defense */
        {0.4, 0.6}   /* 40% probability, 60% defense */
    };
    incorrect_result = incorrect_dynamic_bcra(base_cost, max_cost, moderate_threats, 3, &nash);
    correct_result = correct_dynamic_bcra(base_cost, max_cost, moderate_threats, 3, &nash);
    
    /* Show intermediate calculations */
    printf("  Growth functions:\n");
    for (int i = 0; i < 3; i++) {
        printf("    g(%.1f, %.1f) = %.4f\n", 
               moderate_threats[i].threat_probability,
               moderate_threats[i].defense_effectiveness,
               growth_function(moderate_threats[i].threat_probability,
                             moderate_threats[i].defense_effectiveness));
    }
    
    double sum = incorrect_threat_sum(moderate_threats, 3);
    double product = correct_threat_product(moderate_threats, 3);
    printf("  Sum of growth functions:     %.4f\n", sum);
    printf("  Product of growth functions: %.4f\n", product);
    printf("  exp(product):                %.4f\n", exp(product));
    printf("  Incorrect formula: %.2f\n", incorrect_result);
    printf("  Correct formula:   %.2f\n", correct_result);
    printf("  Difference:        %.2f\n\n", correct_result - incorrect_result);
    
    /* Test Case 4: High threat scenario */
    printf("Test Case 4: High threat scenario\n");
    threat_t high_threats[] = {
        {0.8, 0.2},  /* 80% probability, 20% defense */
        {0.9, 0.1},  /* 90% probability, 10% defense */
        {0.7, 0.3},  /* 70% probability, 30% defense */
        {0.85, 0.15} /* 85% probability, 15% defense */
    };
    incorrect_result = incorrect_dynamic_bcra(base_cost, max_cost, high_threats, 4, &nash);
    correct_result = correct_dynamic_bcra(base_cost, max_cost, high_threats, 4, &nash);
    
    sum = incorrect_threat_sum(high_threats, 4);
    product = correct_threat_product(high_threats, 4);
    printf("  Sum of growth functions:     %.4f\n", sum);
    printf("  Product of growth functions: %.4f\n", product);
    printf("  exp(product):                %.4f\n", exp(product));
    printf("  Incorrect formula: %.2f (capped at max_cost)\n", incorrect_result);
    printf("  Correct formula:   %.2f (capped at max_cost)\n", correct_result);
    printf("  Both hit max_cost cap\n\n");
    
    /* Scaling behavior analysis */
    printf("Scaling Behavior Analysis\n");
    printf("------------------------\n");
    printf("Number of threats vs Cost (p=0.5, E=0.5 for all threats)\n");
    printf("Threats | Incorrect (Sum) | Correct (Product) | Ratio\n");
    printf("--------|----------------|-------------------|-------\n");
    
    for (int n = 0; n <= 5; n++) {
        threat_t uniform_threats[5];
        for (int i = 0; i < n; i++) {
            uniform_threats[i].threat_probability = 0.5;
            uniform_threats[i].defense_effectiveness = 0.5;
        }
        
        incorrect_result = incorrect_dynamic_bcra(base_cost, max_cost, uniform_threats, n, &nash);
        correct_result = correct_dynamic_bcra(base_cost, max_cost, uniform_threats, n, &nash);
        double ratio = (incorrect_result > 0) ? correct_result / incorrect_result : 0;
        
        printf("   %d    |    %8.2f    |     %8.2f     | %.2fx\n", 
               n, incorrect_result, correct_result, ratio);
    }
    
    printf("\n");
    
    /* Key differences */
    printf("Key Differences:\n");
    printf("===============\n");
    printf("1. INCORRECT formula uses SUM: Linear growth with number of threats\n");
    printf("2. CORRECT formula uses PRODUCT with exp(): Exponential growth\n");
    printf("3. INCORRECT has minimum bound of 10, CORRECT has no minimum\n");
    printf("4. INCORRECT: CA(t) = max(10, min(C_max, C_base × Σg(p_i,E_i) × Π_nash))\n");
    printf("5. CORRECT: CA(t) = min(C_max, C_base × exp(∏g(p_i,E_i)) × Π_nash)\n");
}

int main() {
    analyze_formulas();
    return 0;
}