
from bplib.bp import BpGroup, G1Elem, G2Elem, GTElem
from petlib.bn import Bn
from hashlib import sha256


def main():
    parameter = set_params()
    cg, g1, g2, e, n, m, Zq = parameter
    sk_ip, pk_ip = IPKeyGen(parameter)
    sk_u, pk_u = UKeyGen(parameter)
    (alpha, A) = sk_u
    sk_sp, pk_sp = SPKeyGen(parameter)
    tr = []
    for i in range(n):
        r_i = Zq.random()
        tr.append(r_i)
    Er , Rho = Encrypt(parameter, tr, pk_u)
    hu, sigma_r, G, Hu = Sign(parameter, sk_ip, A, tr, Rho)
    b1 = VerifySig(parameter, pk_ip, Er, sigma_r)
    v1 = Zq.random()
    v2 = Zq.random()
    V2 = (v1 * v2) * hu
    Er_p, sigma_r_p, sk_u_p, pk_u_p, G_p = Enroll(parameter, Er, sigma_r, sk_u, pk_u, G, Hu, v1, V2)
    alpha_p, A_p = sk_u_p
    b2 = Verify(parameter, Er_p, sigma_r_p, pk_ip, v2)
    Te = []
    for i in range(n):
        t_i = Zq.random()
        Te.append(t_i)
    Edu, Edu_p, Eksp, gamma, z1, Gz1, Gam, Mu = ComputeD(parameter, Er_p, Te, pk_u_p, pk_sp)
    Edsp, G2, Gz2 = ReEncrypt(parameter, Edu_p, alpha_p, Eksp, G_p, Gz1)
    d = Zq.random()
    delta = d * g2
    b3, b4 = Decide(parameter, Edsp, Edu, sk_sp, pk_sp, pk_u_p, G2, Gz2, gamma, z1, Gam, Te, delta)
    print(b1, b2, b3, b4)



# --------------------------------------------Setup phase-------------------------------------------#

# -----------generate the group public parameters--------------#
def set_params():
    cg = BpGroup()
    g1, g2 = cg.gen1(), cg.gen2()
    e, Zq = cg.pair, cg.order()
    n = 3
    m = []
    for element in range(n):
        m.append(Zq.random())
    return cg, g1, g2, e, n, m, Zq


# -----------generate the pair of keys of the identity provider--------------#
def IPKeyGen(params):
    cg, g1, g2, e, n, m, Zq = params
    (x, y) = Zq.random(), Zq.random()
    sk_ip = (x, y)
    pk_ip = (x * g2, y * g2)
    return sk_ip, pk_ip


# -----------generate the pair of keys of the user--------------#
def UKeyGen(params):
    cg, g1, g2, e, n, m, Zq = params
    alpha = Zq.random()
    sk_u = (alpha, alpha * g1)
    pk_u = alpha * g2
    return sk_u, pk_u

# -----------generate the pair of keys of the service provider--------------#
def SPKeyGen(params):
    cg, g1, g2, e, n, m, Zq = params
    beta = Zq.random()
    sk_sp = beta
    pk_sp = beta * g2
    return sk_sp, pk_sp


# --------------------------------------------Identity_Issue phase-------------------------------------------#


# -----------generate an encrypted template--------------#
def Encrypt(params, Tr, pk_u):
    cg, g1, g2, e, n, m, Zq = params
    Er = []
    Rho = []
    for i in range(n):
        rho_i = Zq.random()
        c1 = rho_i * g2
        c2 = (rho_i * pk_u) + Tr[i] * g2
        Rho.append(rho_i)
        Er.append((c1, c2))
    return Er, Rho


# -----------sign the message m w.r.t. the encrypted template--------------#
def Sign(params, sk_ip, A, tr, Rho):
    cg, g1, g2, e, n, m, Zq = params
    (x, y) = sk_ip
    tu = Zq.random()
    hu = tu * g1
    au = hu
    G = []
    H = []
    a = Rho[0] + ((y + tr[0]) * m[0])
    expp = (tu * Rho[0] * m[0])
    b = expp * A
    G.append(Rho[0] * g1)
    H.append(Rho[0] * hu)
    for i in range(n):
        if i != 0:
            a = a + Rho[i] + ((y + tr[i]) * m[i])
            exp = tu * Rho[i] * m[i]
            b = b + (exp * A)
            G.append(Rho[i] * g1)
            H.append(Rho[i] * hu)
    bu = ((x + a) * hu) + b
    sigma_r = (au, bu)
    return hu, sigma_r, G, H


# -----------verify the signature over the message m w.r.t. the encrypted template--------------#
def VerifySig(params, pk_ip, Er, sigma_r):
    cg, g1, g2, e, n, m, Zq = params
    (X, Y) = pk_ip
    (au, bu) = sigma_r
    a1 = Er[0][0] + ((Y + Er[0][1]) * m[0])
    for i in range(n):
        if i != 0:
            a1 = a1 + (Er[i][0] + ((Y + Er[i][1]) * m[i]))
    pair1 = e(au, X + a1)
    pair2 = e(bu, g2)
    return pair1.eq(pair2)  # e(au, X + a1) == e(bu, g2)


# --------------------------------------------Enrollment phase-------------------------------------------#


# -----------randomize credentials for enrollment at SP--------------#
def Enroll(params, Er, sigma_r, sk_u, pk_u, G, H, v1, V2):
    cg, g1, g2, e, n, m, Zq = params
    alpha, A = sk_u
    au, bu = sigma_r
    k = Zq.random()
    pk_u_p = k * pk_u
    alpha_p = k * alpha
    A_p = k * A
    sk_u_p = (alpha_p, A_p)
    Er_p = []
    G_p = []
    k_inv = k.mod_inverse(Zq)
    a = 0
    HH = (k_inv - 1) * H[0]
    for i in range(n):
        rho_p_i = Zq.random()
        c1_p = k_inv * (Er[i][0] + (rho_p_i * g2))
        c2_p = Er[i][1] + (rho_p_i * pk_u)
        Er_p.append((c1_p, c2_p))
        g_p_i = k_inv * (G[i] + (rho_p_i * g1))
        G_p.append(g_p_i)
        a = a + k_inv * rho_p_i + alpha * rho_p_i * m[i]
        if i != 0:
            HH = HH + (k_inv - 1) * H[i]
    t = Zq.random()
    v1_inv = v1.mod_inverse(Zq)
    au_p = (t * v1_inv) * V2
    bu_p = t * (bu + a * au + HH)
    sigma_r_p = (au_p, bu_p)
    return Er_p, sigma_r_p, sk_u_p, pk_u_p, G_p


def Verify(params, Er_p, sigma_r_p, pk_ip, v2):
    cg, g1, g2, e, n, m, Zq = params
    (X, Y) = pk_ip
    (au, bu) = sigma_r_p
    a1 = Er_p[0][0] + ((Y + Er_p[0][1]) * m[0])
    for i in range(n):
        if i != 0:
            a1 = a1 + (Er_p[i][0] + ((Y + Er_p[i][1]) * m[i]))
    pair1 = e(au, X + a1)
    pair2 = e(bu, g2) ** v2
    return pair1.eq(pair2)


# --------------------------------------------Verification phase-------------------------------------------#


# -----------homomorphically compute an Hamming distance--------------#

def HomoDis(params, Er, Te, pk_u):
    cg, g1, g2, e, n, m, Zq = params
    Ee, Gam = Encrypt(params, Te, pk_u)
    D_1 = (1 - 2 * Te[0]) * Er[0][0] + Ee[0][0]
    D_2 = (1 - 2 * Te[0]) * Er[0][1] + Ee[0][1]
    for i in range(n):
        if i != 0:
            D_i_1 =  (1 - 2 * Te[i]) * Er[i][0] + Ee[i][0]
            D_i_2 = (1 - 2 * Te[i]) * Er[i][1] + Ee[i][1]
            D_1 = D_1 + D_i_1
            D_2 = D_2 + D_i_2
    Edu = (D_1, D_2)
    return Ee, Gam, Edu


# -----------compute a randomized Hamming distance--------------#

def ComputeD(params, Er, Te, pk_u, pk_sp):
    cg, g1, g2, e, n, m, Zq = params
    Ee, Gam, Edu = HomoDis(params, Er, Te, pk_u)
    mu = Zq.random()
    Mu = mu * g2
    D_1, D_2 = Edu
    Edu_p = (D_1, D_2 + Mu)
    gamma = Zq.random()
    Eksp = (gamma * g2, gamma * pk_sp + Mu)
    z1 = Zq.random()
    Gz1 = z1 * g1
    return Edu, Edu_p, Eksp, gamma, z1, Gz1, Gam, mu


# -----------decrypt a ciphertext--------------#

def decrypt(C, sk):
    c1, c2 = C
    m = c2 - (sk * c1)
    return m


# -----------blindly re-encrypt a message--------------#

def ReEncrypt(params, Edu, sk_u, Eksp, G, Gz1):
    cg, g1, g2, e, n, m, Zq = params
    Dh_p = decrypt(Edu, sk_u)
    c1 , c2 = Eksp
    Edsp = (c1.neg(), Dh_p + c2.neg())
    z2 = Zq.random()
    G2 = []
    for i in range(n):
        G2.append(z2 * G[i])
    Gz2 = z2 * Gz1
    return Edsp, G2, Gz2


# -----------Take the authentication decision--------------#

def Decide(params, Edsp, Edu, sk_sp, pk_sp, pk_u, G, Gz2, gamma, z1, Gam, Te, delta):
    cg, g1, g2, e, n, m, Zq = params
    phi1, theta1 = Edsp
    phi2, theta2 = Edu
    psi1 = - gamma * pk_u
    psi2 = sk_sp * phi2
    ter1 = (theta1 - theta2) + (psi2 - psi1)
    pair1 = e(Gz2, ter1)
    sum_gam = Gam[0]
    a = (z1 * (1 - 2 * Te[0])) * G[0]
    for i in range(n):
        if i != 0:
            sum_gam = sum_gam + Gam[i]
            a = a + (z1 * (1 - 2 * Te[i])) * G[i]
    ter2 = ((sum_gam - gamma) * Gz2) + a
    pair2 = e(ter2, pk_sp - pk_u)
    res1 = pair1.eq(pair2)
    if not res1:
        res2 = 0
        Dh = decrypt(Edsp, sk_sp)
    else:
        Dh = decrypt(Edsp, sk_sp)
        if Dh.add(delta.neg()).isinf():
            res2 = 1
        else:
            res2 = 0
    return res1, res2



if __name__ == '__main__':
    main()


