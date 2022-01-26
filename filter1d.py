import random

eps = 1/12
sigma = 200
var = sigma**2
N = 12000
X = [random.gauss(10000,var) for i in range(N//12)]+[random.gauss(0,sigma) for i in range(N*11//12)]

def trimmed_mean(X, eps):
    N = len(X)
    Y = sorted(X)[int(N*eps*2):-int(N*eps*2)]
    return sum(Y)/len(Y)

def filter1d(X, var):
    N = len(X)
    C = [1 for i in range(N)]
    while True:
        mu_hat = sum(C[i] * X[i] for i in range(N)) / sum(C)
        tau = [(X[i] - mu_hat)**2 for i in range(N)]
        var_hat = sum(C[i] * tau[i] for i in range(N)) / sum(C)
        print("{:.2e}\t{:.2f}\t{:.2f}\t{:.2f}".format(
            var_hat,
            mu_hat,
            sum(C[i]*tau[i] for i in range(N//12))/N/var_hat,
            sum(C[i]*tau[i] for i in range(N//12, N))/N/var_hat
        ))
        if var_hat <= 16*var: return mu_hat
        tau_max = max(tau)
        C = [C[i] * (1-tau[i]/tau_max) for i in range(N)]


print("filter1d     =", filter1d(X, var))
print("trimmed_mean =", trimmed_mean(X, eps))
print("average      =", sum(X)/len(X))